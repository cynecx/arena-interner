use std::{
    cell::RefCell,
    collections::hash_map::{Entry, VacantEntry},
    fmt,
    hash::{Hash, Hasher},
    marker::PhantomData,
    ops::Deref,
};

pub use bumpalo::Bump;

type HashMap<K, V> = ahash::HashMap<K, V>;

#[derive(Clone, Copy)]
pub struct Interned<'a, 'g>(&'a str, generativity::Id<'g>);

impl<'a, 'g> Interned<'a, 'g> {
    #[inline]
    pub fn as_str(&self) -> &'a str {
        self.0
    }
}

impl Deref for Interned<'_, '_> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &str {
        self.0
    }
}

impl PartialEq for Interned<'_, '_> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        // SAFETY: We compare the interned values which have stable addresses.
        // We also rely on "generativity" / "unique invariant lifetimes" to prevent comparison
        // of unrelated arena allocated `Interned`s.
        self.0.as_ptr() == other.0.as_ptr()
    }
}

impl Eq for Interned<'_, '_> {}

impl Hash for Interned<'_, '_> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.as_ptr().hash(state);
    }
}

impl fmt::Display for Interned<'_, '_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.0, f)
    }
}

impl fmt::Debug for Interned<'_, '_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.0, f)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CowStr<'b> {
    Borrowed(&'b str),
    Owned(bumpalo::collections::String<'b>),
}

impl<'b> From<bumpalo::collections::String<'b>> for CowStr<'b> {
    #[inline]
    fn from(val: bumpalo::collections::String<'b>) -> Self {
        Self::Owned(val)
    }
}

impl<'b> From<&'b str> for CowStr<'b> {
    #[inline]
    fn from(val: &'b str) -> Self {
        Self::Borrowed(val)
    }
}

macro_rules! internable_integers {
    ($t:ty, $($ts:ty),+) => {
        internable_integers!($t);
        internable_integers!($($ts),+);
    };
    ($t:ty) => {
        impl Internable for $t {
            #[inline]
            fn intern<'b>(&self, arena: &'b Bump) -> CowStr<'b> {
                bumpalo::format!(in arena, "{}", self).into()
            }
        }
    };
}

pub trait Internable: Copy + Clone + Hash + PartialEq + Eq {
    fn intern<'b>(&self, arena: &'b Bump) -> CowStr<'b>;
}

internable_integers!(isize, i8, i16, i32, i64, usize, u8, u16, u32, u64);

#[repr(transparent)]
struct UnsafeBumpRefStr(*const str);

impl Hash for UnsafeBumpRefStr {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        // SAFETY: `UnsafeBumpRefStr` must not outlive the bump allocator.
        let slice = unsafe { &*self.0 };
        slice.hash(state);
    }
}

impl PartialEq for UnsafeBumpRefStr {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        if self.0 == other.0 {
            return true;
        }
        // SAFETY: `UnsafeBumpRefStr` must not outlive the bump allocator.
        let slice_a = unsafe { &*self.0 };
        let slice_b = unsafe { &*other.0 };
        slice_a == slice_b
    }
}

impl Eq for UnsafeBumpRefStr {}

pub struct Storage {
    // Drop the `map` first, then the bump allocator `arena`.
    // SAFETY: `UnsafeBumpRefStr` is a reference into the bump allocator `arena`.
    map: RefCell<HashMap<UnsafeBumpRefStr, ()>>,
    arena: Bump,
    _not_sync: PhantomData<*const ()>,
}

unsafe impl Send for Storage {}

impl Storage {
    pub fn new() -> Self {
        Self {
            arena: Bump::new(),
            map: RefCell::new(HashMap::default()),
            _not_sync: PhantomData,
        }
    }
}

pub struct Interner<'s, 'g> {
    storage: &'s Storage,
    id: generativity::Id<'g>,
}

unsafe impl<'s, 'g> Send for Interner<'s, 'g> {}

impl<'s, 'g> Interner<'s, 'g> {
    pub fn new(storage: &'s mut Storage, guard: generativity::Guard<'g>) -> Self {
        Self {
            storage,
            id: guard.into(),
        }
    }

    #[inline]
    pub fn intern(&self, val: &str) -> Interned<'s, 'g> {
        // SAFETY: We don't store this instance of `UnsafeBumpRefStr` inside our state.
        //         We just use it for the hashmap lookup.
        if let Some((entry, _)) = self
            .storage
            .map
            .borrow()
            .get_key_value(&UnsafeBumpRefStr(val as *const str))
        {
            let interned = unsafe {
                // SAFETY: We only store bump allocator references inside the inner map.
                &*entry.0
            };
            return Interned(interned, self.id);
        }
        self.intern_slow(val)
    }

    #[cold]
    fn intern_slow(&self, val: &str) -> Interned<'s, 'g> {
        // Note: Reborrow here which "downgrades" the mutable reference. This makes miri happy.
        let interned = &*self.storage.arena.alloc_str(val);
        let prev = self
            .storage
            .map
            .borrow_mut()
            .insert(UnsafeBumpRefStr(interned as *const str), ());
        assert!(prev.is_none());
        Interned(interned, self.id)
    }

    pub fn typed_interner<'a, K: Internable>(&'a mut self) -> TypedInterner<'a, 's, 'g, K> {
        TypedInterner {
            inner: self,
            map: RefCell::new(HashMap::default()),
        }
    }
}

pub struct TypedInterner<'a, 's, 'g, K> {
    inner: &'a Interner<'s, 'g>,
    map: RefCell<HashMap<K, *const str>>,
}

/// SAFETY: For this to be sound and ergonomic, [`Interner::typed_interner`]
/// must take a mutable self reference.
unsafe impl<'a, 's, 'g, K: Internable> Send for TypedInterner<'a, 's, 'g, K> {}

impl<'a, 's, 'g, K: Internable> TypedInterner<'a, 's, 'g, K> {
    #[inline]
    pub fn intern(&self, val: K) -> Interned<'s, 'g> {
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

    #[inline]
    pub fn intern_str(&self, val: &str) -> Interned<'s, 'g> {
        self.inner.intern(val)
    }

    #[cold]
    fn intern_slow(&self, vacant: VacantEntry<K, *const str>, val: K) -> Interned<'s, 'g> {
        let mut inner_map = self.inner.storage.map.borrow_mut();
        let (is_new, interned_ptr) = match val.intern(&self.inner.storage.arena) {
            CowStr::Borrowed(val) => {
                match inner_map.get_key_value(&UnsafeBumpRefStr(val as *const str)) {
                    Some((entry, _)) => (false, entry.0),
                    None => (true, val as *const str),
                }
            }
            CowStr::Owned(val) => {
                match inner_map.get_key_value(&UnsafeBumpRefStr(val.as_str() as *const str)) {
                    Some((entry, _)) => (false, entry.0),
                    None => (true, val.into_bump_str() as *const str),
                }
            }
        };
        if is_new {
            let prev = inner_map.insert(UnsafeBumpRefStr(interned_ptr), ());
            assert!(prev.is_none());
        }
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

pub trait OptionInternExt: private::Sealed {
    fn intern_in<'s, 'g>(&self, interner: &Interner<'s, 'g>) -> Option<Interned<'s, 'g>>;
}

impl<'a> OptionInternExt for Option<&'a str> {
    #[inline]
    fn intern_in<'s, 'g>(&self, interner: &Interner<'s, 'g>) -> Option<Interned<'s, 'g>> {
        self.map(|val| interner.intern(val))
    }
}

impl OptionInternExt for Option<String> {
    #[inline]
    fn intern_in<'s, 'g>(&self, interner: &Interner<'s, 'g>) -> Option<Interned<'s, 'g>> {
        self.as_deref().map(|val| interner.intern(val))
    }
}

pub trait OptionTypedInternExt<I>: private::Sealed
where
    I: Internable,
{
    fn intern_in<'s, 'g>(self, interner: &TypedInterner<'_, 's, 'g, I>)
        -> Option<Interned<'s, 'g>>;
}

impl<T: Internable> OptionTypedInternExt<T> for Option<T> {
    #[inline]
    fn intern_in<'s, 'g>(
        self,
        interner: &TypedInterner<'_, 's, 'g, T>,
    ) -> Option<Interned<'s, 'g>> {
        self.map(|val| interner.intern(val))
    }
}

impl<'a, T: Internable> OptionTypedInternExt<T> for Option<&'a String> {
    #[inline]
    fn intern_in<'s, 'g>(
        self,
        interner: &TypedInterner<'_, 's, 'g, T>,
    ) -> Option<Interned<'s, 'g>> {
        self.map(|val| interner.intern_str(val))
    }
}

impl<'a, T: Internable> OptionTypedInternExt<T> for Option<&'a str> {
    #[inline]
    fn intern_in<'s, 'g>(
        self,
        interner: &TypedInterner<'_, 's, 'g, T>,
    ) -> Option<Interned<'s, 'g>> {
        self.map(|val| interner.intern_str(val))
    }
}

impl<T: Internable> private::Sealed for Option<T> {}

impl private::Sealed for Option<String> {}

impl<'a> private::Sealed for Option<&'a String> {}

impl<'a> private::Sealed for Option<&'a str> {}

mod private {
    pub trait Sealed {}
}

#[doc(hidden)]
pub mod internal {
    pub use generativity;
}

#[macro_export]
macro_rules! make_interner {
    ($name:ident) => {
        $crate::internal::generativity::make_guard!(guard);
        let mut storage = $crate::Storage::new();
        let $name = $crate::Interner::new(&mut storage, guard);
    };
    (mut $name:ident) => {
        $crate::internal::generativity::make_guard!(guard);
        let mut storage = $crate::Storage::new();
        let mut $name = $crate::Interner::new(&mut storage, guard);
    };
}

#[cfg(test)]
mod tests {
    use super::Interned;

    #[test]
    fn layout() {
        assert_eq!(
            std::mem::size_of::<Interned<'static, 'static>>(),
            std::mem::size_of::<*const str>(),
        );
        assert_eq!(
            std::mem::size_of::<Option<Interned<'static, 'static>>>(),
            std::mem::size_of::<*const str>(),
        );
    }

    #[test]
    fn interner_strings() {
        make_interner!(interner);

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
            assert_eq!(&*a, &*b);
            assert_eq!(a.as_ptr(), b.as_ptr());
        }
    }

    #[test]
    fn interner_ints() {
        make_interner!(mut interner);
        let int_interner = interner.typed_interner();

        let vals = &[
            0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 0xFF, 0xFFFF, 0xFFFFFF, 0xFFFFFFF, -1, -2, -3, -4, -5,
            -6, -8, -9, -10, -0xFF, -0xFFFF, -0xFFFFFF,
        ];

        for &val in vals {
            let a = int_interner.intern(val);
            let b = int_interner.intern(val);

            assert_eq!(a, b);
            assert_eq!(&*a, &*b);
            assert_eq!(a.as_ptr(), b.as_ptr());

            let s = &*format!("{}", val);
            let c = int_interner.intern_str(s);

            assert_eq!(a, c);
            assert_eq!(&*a, &*c);
            assert_eq!(a.as_ptr(), c.as_ptr());
        }
    }

    #[test]
    fn intern_after_typed_drop_ptr() {
        make_interner!(mut interner);
        let a = interner.typed_interner::<i32>().intern(42).as_ptr();
        let b = interner.typed_interner::<i32>().intern(42).as_ptr();
        assert_eq!(a, b);
    }

    #[test]
    fn intern_after_typed_drop() {
        make_interner!(mut interner);
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
            make_interner!(mut interner);
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
        make_interner!(mut interner);
        let int_interner = interner.typed_interner::<i32>();
        std::thread::scope(|scope| {
            let _handle = scope.spawn(move || {
                int_interner.intern(1);
            });
        });
    }

    #[test]
    fn option_ext() {
        use super::OptionInternExt;
        make_interner!(interner);
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
        make_interner!(mut interner);
        let interner = interner.typed_interner::<i32>();
        assert_eq!(
            Some(123).intern_in(&interner),
            Some(interner.intern_str("123"))
        );
        assert_eq!(
            Some("123").intern_in(&interner),
            Some(interner.intern_str("123"))
        );
    }

    #[test]
    fn storage_lifetime() {
        make_interner!(mut interner);
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
