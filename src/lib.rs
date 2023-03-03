use std::{
    cell::RefCell,
    fmt,
    hash::{Hash, Hasher},
    marker::PhantomData,
};

use bumpalo::Bump;
use hashbrown::{
    hash_map::{DefaultHashBuilder, Entry, RawEntryMut, RawVacantEntryMut, VacantEntry},
    HashMap,
};

#[derive(Clone, Copy)]
pub struct Interned<'s, 'g, I: ?Sized>(pub &'s I, generativity::Id<'g>);

impl<'s, 'g, I: ?Sized> Interned<'s, 'g, I> {
    #[inline]
    pub fn as_ptr(&self) -> *const I {
        self.0 as *const I
    }
}

impl<'s, 'g, I: ?Sized> PartialEq for Interned<'s, 'g, I> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        // SAFETY: We compare the interned values which have stable addresses / locations.
        // We also rely on "generativity" / "unique invariant lifetimes" to prevent comparison
        // of unrelated arena allocated `Interned`s.
        (self.0 as *const I) == (other.0 as *const I)
    }
}

impl<'s, 'g, I: ?Sized> Eq for Interned<'s, 'g, I> {}

impl<'s, 'g, I: ?Sized> Hash for Interned<'s, 'g, I> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.0 as *const I).hash(state);
    }
}

impl<'s, 'g, I: ?Sized + fmt::Display> fmt::Display for Interned<'s, 'g, I> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.0, f)
    }
}

impl<'s, 'g, I: ?Sized + fmt::Debug> fmt::Debug for Interned<'s, 'g, I> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.0, f)
    }
}

pub trait Intern: Hash + PartialEq + Eq {
    fn intern<'b>(&self, arena: &'b Bump) -> &'b Self;
}

#[repr(transparent)]
struct UnsafeBumpRef<I: ?Sized>(*const I);

impl<I: ?Sized + Intern> Hash for UnsafeBumpRef<I> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        // SAFETY: `UnsafeBumpRefStr` must not outlive the bump allocator.
        let r = unsafe { &*self.0 };
        r.hash(state);
    }
}

impl<I: ?Sized + Intern> PartialEq for UnsafeBumpRef<I> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        // SAFETY: `UnsafeBumpRefStr` must not outlive the bump allocator.
        let a = unsafe { &*self.0 };
        let b = unsafe { &*other.0 };
        a == b
    }
}

impl<I: ?Sized + Intern> Eq for UnsafeBumpRef<I> {}

pub struct Storage<I: ?Sized> {
    // Drop the `map` first, then the bump allocator `arena`.
    // SAFETY: `UnsafeBumpRefStr` is a reference into the bump allocator `arena`. We have to resort
    // to using unsafe here since self-referential structs in Rust is tricky business.
    map: RefCell<HashMap<UnsafeBumpRef<I>, ()>>,
    arena: Bump,
    // The storage is explicitly not `Sync` (but `Send`, see below).
    _not_sync: PhantomData<*const ()>,
}

// SAFETY: `Storage` is `Send` but not `Sync`. This is safe because the `Interner` mutably borrows
// `Storage` and the `Interner` itself is also `Send` but not `Sync`.
unsafe impl<I: ?Sized> Send for Storage<I> {}

impl<I: ?Sized + Intern> Storage<I> {
    pub fn new() -> Self {
        Self {
            arena: Bump::new(),
            map: RefCell::new(HashMap::default()),
            _not_sync: PhantomData,
        }
    }
}

impl<I: ?Sized + Intern> Default for Storage<I> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

pub struct Interner<'s, 'g, I: ?Sized> {
    storage: &'s Storage<I>,
    id: generativity::Id<'g>,
    _intern: PhantomData<I>,
}

unsafe impl<'s, 'g, I: ?Sized + Intern> Send for Interner<'s, 'g, I> {}

impl<'s, 'g, I: Intern + ?Sized> Interner<'s, 'g, I> {
    pub fn new(storage: &'s mut Storage<I>, guard: generativity::Guard<'g>) -> Self {
        Self {
            storage,
            id: guard.into(),
            _intern: PhantomData,
        }
    }

    pub fn intern(&self, val: &I) -> Interned<'s, 'g, I> {
        // SAFETY: We don't store this instance of `UnsafeBumpRefStr` inside our state.
        //         We just use it for the hashmap lookup.
        match self
            .storage
            .map
            .borrow_mut()
            .raw_entry_mut()
            .from_key(&UnsafeBumpRef(val as *const I))
        {
            RawEntryMut::Occupied(occupied) => {
                Interned(
                    unsafe {
                        // SAFETY: We only store bump allocator references inside the inner map.
                        &*occupied.key().0
                    },
                    self.id,
                )
            }
            RawEntryMut::Vacant(vacant) => self.intern_slow(vacant, val),
        }
    }

    #[cold]
    fn intern_slow(
        &self,
        vacant: RawVacantEntryMut<UnsafeBumpRef<I>, (), DefaultHashBuilder>,
        val: &I,
    ) -> Interned<'s, 'g, I> {
        let arena_val = Intern::intern(val, &self.storage.arena);
        // SAFETY: This is safe because this reference doesn't outlive the bump allocator.
        vacant.insert(UnsafeBumpRef(arena_val as *const I), ());
        Interned(arena_val, self.id)
    }

    pub fn typed_interner<'a, K: InternInto<I>>(&'a mut self) -> TypedInterner<'a, 's, 'g, I, K> {
        TypedInterner {
            inner: self,
            map: RefCell::new(HashMap::default()),
        }
    }
}

#[macro_export]
macro_rules! make_interner {
    ($name:ident : $ty:ty) => {
        $crate::internal::generativity::make_guard!(guard);
        let mut storage = $crate::Storage::new();
        let $name = $crate::Interner::<'_, '_, $ty>::new(&mut storage, guard);
    };
    (mut $name:ident : $ty:ty) => {
        $crate::internal::generativity::make_guard!(guard);
        let mut storage = $crate::Storage::new();
        let mut $name = $crate::Interner::<'_, '_, $ty>::new(&mut storage, guard);
    };
}

// ---

#[derive(Debug)]
pub enum CowBox<'b, I: ?Sized, Owned: IntoBumpRef<'b, I>> {
    Borrowed(&'b I),
    Owned(Owned),
}

impl<'b, I: ?Sized, Owned: IntoBumpRef<'b, I>> CowBox<'b, I, Owned> {
    #[inline]
    pub fn as_ref(&self) -> &I {
        match self {
            Self::Borrowed(borrowed) => *borrowed,
            Self::Owned(owned) => owned.as_bump_ref(),
        }
    }
}

pub trait IntoBumpRef<'b, T: ?Sized + 'b> {
    fn as_bump_ref(&self) -> &T;

    fn into_bump_ref(self) -> &'b T;
}

impl<'b, T: ?Sized + 'b> IntoBumpRef<'b, T> for bumpalo::boxed::Box<'b, T> {
    #[inline]
    fn as_bump_ref(&self) -> &T {
        self.as_ref()
    }

    #[inline]
    fn into_bump_ref(self) -> &'b T {
        bumpalo::boxed::Box::leak(self)
    }
}

impl<'b> IntoBumpRef<'b, str> for bumpalo::collections::String<'b> {
    #[inline]
    fn as_bump_ref(&self) -> &str {
        self.as_str()
    }

    #[inline]
    fn into_bump_ref(self) -> &'b str {
        self.into_bump_str()
    }
}

impl<'b, T> IntoBumpRef<'b, [T]> for bumpalo::collections::Vec<'b, T> {
    #[inline]
    fn as_bump_ref(&self) -> &[T] {
        self.as_slice()
    }

    #[inline]
    fn into_bump_ref(self) -> &'b [T] {
        self.into_bump_slice()
    }
}

pub trait InternInto<I: ?Sized>: Copy + Clone + Hash + PartialEq + Eq {
    type Owned<'b>: IntoBumpRef<'b, I>
    where
        I: 'b;

    fn intern_into<'b>(&self, arena: &'b Bump) -> CowBox<'b, I, Self::Owned<'b>>;
}

macro_rules! internable_integers {
    ($t:ty, $($ts:ty),+) => {
        internable_integers!($t);
        internable_integers!($($ts),+);
    };
    ($t:ty) => {
        impl InternInto<str> for $t {
            type Owned<'b> = bumpalo::collections::String<'b>;

            #[inline]
            fn intern_into<'b>(&self, arena: &'b Bump) -> CowBox<'b, str, Self::Owned<'b>> {
                CowBox::Owned(bumpalo::format!(in arena, "{}", *self))
            }
        }
    };
}

internable_integers!(isize, i8, i16, i32, i64, i128, usize, u8, u16, u32, u64, u128);

// ---

impl Intern for str {
    #[inline]
    fn intern<'b>(&self, arena: &'b Bump) -> &'b Self {
        arena.alloc_str(self)
    }
}

// ---

pub struct TypedInterner<'a, 's, 'g, I: ?Sized, K> {
    inner: &'a Interner<'s, 'g, I>,
    map: RefCell<HashMap<K, *const I>>,
}

/// SAFETY: For this to be sound and ergonomic, [`Interner::typed_interner`]
/// must take a mutable self reference.
unsafe impl<'a, 's, 'g, I: ?Sized + Intern, K: InternInto<I>> Send
    for TypedInterner<'a, 's, 'g, I, K>
{
}

impl<'a, 's, 'g, I: ?Sized + Intern, K: InternInto<I>> TypedInterner<'a, 's, 'g, I, K> {
    #[inline]
    pub fn intern_raw(&self, val: &I) -> Interned<'s, 'g, I> {
        self.inner.intern(val)
    }

    #[inline]
    pub fn intern(&self, val: K) -> Interned<'s, 'g, I> {
        match self.map.borrow_mut().entry(val) {
            Entry::Occupied(occupied) => {
                Interned(
                    unsafe {
                        // SAFETY: This is a reference into the bump allocator `arena`.
                        &**occupied.get()
                    },
                    self.inner.id,
                )
            }
            Entry::Vacant(vacant) => self.intern_slow(vacant, val),
        }
    }

    #[cold]
    fn intern_slow(
        &self,
        vacant: VacantEntry<'_, K, *const I, DefaultHashBuilder>,
        val: K,
    ) -> Interned<'s, 'g, I> {
        let mut inner_map = self.inner.storage.map.borrow_mut();
        let interned = val.intern_into(&self.inner.storage.arena);
        let interned_ptr =
            match inner_map.get_key_value(&UnsafeBumpRef(interned.as_ref() as *const I)) {
                Some((entry, _)) => entry.0,
                None => {
                    let interned_ptr = match interned {
                        CowBox::Borrowed(val) => val as *const I,
                        CowBox::Owned(val) => val.into_bump_ref() as *const I,
                    };
                    let prev = inner_map.insert(UnsafeBumpRef(interned_ptr), ());
                    assert!(prev.is_none());
                    interned_ptr
                }
            };
        vacant.insert(interned_ptr);
        Interned(
            unsafe {
                // SAFETY: interned_ptr is always derived from a reference that has the lifetime of
                // the bump allocator `'b`.
                &*interned_ptr
            },
            self.inner.id,
        )
    }
}

// ---

pub trait OptionInternExt<I>
where
    I: ?Sized + Intern,
{
    fn intern_in<'s, 'g>(&self, interner: &Interner<'s, 'g, I>) -> Option<Interned<'s, 'g, I>>;
}

impl<'a, I: ?Sized + Intern> OptionInternExt<I> for Option<&'a I> {
    #[inline]
    fn intern_in<'s, 'g>(&self, interner: &Interner<'s, 'g, I>) -> Option<Interned<'s, 'g, I>> {
        self.map(|val| interner.intern(val))
    }
}

impl OptionInternExt<str> for Option<String> {
    #[inline]
    fn intern_in<'s, 'g>(&self, interner: &Interner<'s, 'g, str>) -> Option<Interned<'s, 'g, str>> {
        self.as_deref().map(|val| interner.intern(val))
    }
}

pub trait OptionTypedInternExt<I, K>
where
    I: ?Sized + Intern,
    K: InternInto<I>,
{
    fn intern_in<'s, 'g>(
        self,
        interner: &TypedInterner<'_, 's, 'g, I, K>,
    ) -> Option<Interned<'s, 'g, I>>;
}

impl<I: ?Sized + Intern, K: InternInto<I>> OptionTypedInternExt<I, K> for Option<K> {
    #[inline]
    fn intern_in<'s, 'g>(
        self,
        interner: &TypedInterner<'_, 's, 'g, I, K>,
    ) -> Option<Interned<'s, 'g, I>> {
        self.map(|val| interner.intern(val))
    }
}

pub trait OptionTypedRawInternExt<I, K>
where
    I: ?Sized + Intern,
    K: InternInto<I>,
{
    fn intern_raw_in<'s, 'g>(
        self,
        interner: &TypedInterner<'_, 's, 'g, I, K>,
    ) -> Option<Interned<'s, 'g, I>>;
}

impl<'a, I: ?Sized + Intern, K: InternInto<I>> OptionTypedRawInternExt<I, K> for Option<&'a I> {
    #[inline]
    fn intern_raw_in<'s, 'g>(
        self,
        interner: &TypedInterner<'_, 's, 'g, I, K>,
    ) -> Option<Interned<'s, 'g, I>> {
        self.map(|val| interner.intern_raw(val))
    }
}

#[doc(hidden)]
pub mod internal {
    pub use generativity;
}

#[cfg(test)]
mod tests {
    use crate::OptionTypedRawInternExt;

    use super::Interned;

    #[test]
    fn layout() {
        assert_eq!(
            std::mem::size_of::<Interned<'static, 'static, str>>(),
            std::mem::size_of::<*const str>(),
        );
        assert_eq!(
            std::mem::size_of::<Option<Interned<'static, 'static, str>>>(),
            std::mem::size_of::<*const str>(),
        );
    }

    #[test]
    fn interner_strings() {
        make_interner!(interner: str);

        let vals = &[
            "hello world",
            "world is on fire",
            "but i don't really care",
            "so we yolo through",
            "y",
            "",
        ];

        for &val in vals {
            let a = interner.intern(val);
            let b = interner.intern(val);

            assert_eq!(a, b);
            assert_eq!(a.0, b.0);
            assert_eq!(a.as_ptr(), b.as_ptr());
        }
    }

    #[test]
    fn interner_ints() {
        make_interner!(mut interner: str);
        let int_interner = interner.typed_interner();

        let vals = &[
            0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 0xFF, 0xFFFF, 0xFFFFFF, 0xFFFFFFF, -1, -2, -3, -4, -5,
            -6, -8, -9, -10, -0xFF, -0xFFFF, -0xFFFFFF,
        ];

        for &val in vals {
            let a = int_interner.intern(val);
            let b = int_interner.intern(val);

            assert_eq!(a, b);
            assert_eq!(a.0, b.0);
            assert_eq!(a.as_ptr(), b.as_ptr());

            let s = &*format!("{}", val);
            let c = int_interner.intern_raw(s);

            assert_eq!(a, c);
            assert_eq!(a.0, c.0);
            assert_eq!(a.as_ptr(), c.as_ptr());
        }
    }

    #[test]
    fn interner_ints_reverse_order() {
        make_interner!(mut interner: str);
        let int_interner = interner.typed_interner();

        let vals = &[
            0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 0xFF, 0xFFFF, 0xFFFFFF, 0xFFFFFFF, -1, -2, -3, -4, -5,
            -6, -8, -9, -10, -0xFF, -0xFFFF, -0xFFFFFF,
        ];

        for &val in vals {
            // Intern a string before using the typed interner.
            let s = &*format!("{}", val);
            let c = int_interner.intern_raw(s);

            let a = int_interner.intern(val);
            let b = int_interner.intern(val);

            assert_eq!(a, b);
            assert_eq!(a.0, b.0);
            assert_eq!(a.as_ptr(), b.as_ptr());

            assert_eq!(a, c);
            assert_eq!(a.0, c.0);
            assert_eq!(a.as_ptr(), c.as_ptr());
        }
    }

    #[test]
    fn intern_after_typed_drop_ptr() {
        make_interner!(mut interner: str);
        let a = interner.typed_interner::<i32>().intern(42).as_ptr();
        let b = interner.typed_interner::<i32>().intern(42).as_ptr();
        assert_eq!(a, b);
    }

    #[test]
    fn intern_after_typed_drop() {
        make_interner!(mut interner: str);
        let a = interner.typed_interner::<i32>().intern(23);
        let b = interner.typed_interner::<i32>().intern(23);
        assert_eq!(a, b);
    }

    #[test]
    fn interner_async() {
        fn is_send<T: Send>(val: T) -> T {
            val
        }

        let fut = async {
            make_interner!(mut interner: str);
            let mut int_interner = interner.typed_interner();
            let m = int_interner.intern(100000);
            let r = &mut int_interner;
            let _a: () = std::future::pending().await;
            let _ = r.intern(1);
            m.to_string()
        };

        let _fut = is_send(fut);
    }

    #[test]
    fn interner_threads() {
        make_interner!(mut interner: str);
        let int_interner = interner.typed_interner::<i32>();
        std::thread::scope(|scope| {
            let _handle = scope.spawn(move || {
                int_interner.intern(1);
            });
        });
    }

    #[test]
    fn interner_threads_escape() {
        make_interner!(mut interner: str);
        let mut int_interner = interner.typed_interner::<i32>();
        let (a, b) = std::thread::scope(|scope| {
            let int_interner = &mut int_interner;
            scope
                .spawn(move || (int_interner.intern(1), int_interner.intern(2)))
                .join()
                .unwrap()
        });
        let c = int_interner.intern(1);
        assert_eq!(a, c);
        assert_ne!(b, c);
    }

    #[test]
    fn option_ext() {
        use super::OptionInternExt;
        make_interner!(interner: str);
        assert_eq!(
            Some("hello").intern_in(&interner),
            Some(interner.intern("hello"))
        );
        assert_eq!(
            Some("hello".to_string()).intern_in(&interner),
            Some(interner.intern("hello"))
        );
    }

    #[test]
    fn option_typed_ext() {
        use super::OptionTypedInternExt;
        make_interner!(mut interner: str);
        let interner = interner.typed_interner::<i32>();
        assert_eq!(
            Some(123).intern_in(&interner),
            Some(interner.intern_raw("123"))
        );
        assert_eq!(
            Some("123").intern_raw_in(&interner),
            Some(interner.intern_raw("123"))
        );
    }

    #[test]
    fn storage_lifetime() {
        make_interner!(mut interner: str);
        let (a, b, c) = {
            let a = interner.intern("420");
            let t = interner.typed_interner::<i32>();
            let b = t.intern(420);
            drop(t);
            let t = interner.typed_interner::<i32>();
            let c = t.intern(420);
            (a, b, c)
        };
        assert_eq!(a, b);
        assert_eq!(b, c);
    }
}
