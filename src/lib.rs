use std::{
    cell::RefCell,
    collections::hash_map::{Entry, VacantEntry},
    fmt,
    hash::{Hash, Hasher},
    marker::PhantomData,
    ops::Deref,
};

use bumpalo::Bump;

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

macro_rules! internable_integers {
    ($t:ty, $($ts:ty),+) => {
        internable_integers!($t);
        internable_integers!($($ts),+);
    };
    ($t:ty) => {
        impl Internable for $t {
            #[inline]
            fn intern<'b>(&self, arena: &'b Bump) -> &'b str {
                bumpalo::format!(in arena, "{}", self).into_bump_str()
            }
        }
    };
}

pub trait Internable: Copy + Clone + Hash + PartialEq + Eq {
    fn intern<'b>(&self, arena: &'b Bump) -> &'b str;
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

pub struct Interner<'g> {
    // Drop the `map` first, then the bump allocator `arena`.
    // SAFETY: `UnsafeBumpRefStr` is a reference into the bump allocator `arena`.
    map: RefCell<HashMap<UnsafeBumpRefStr, ()>>,
    arena: Bump,
    id: generativity::Id<'g>,
}

unsafe impl<'g> Send for Interner<'g> {}

impl<'g> Interner<'g> {
    pub fn new(guard: generativity::Guard<'g>) -> Self {
        Self {
            arena: Bump::new(),
            map: RefCell::new(HashMap::default()),
            id: guard.into(),
        }
    }

    #[inline]
    pub fn intern<'a>(&'a self, val: &str) -> Interned<'a, 'g> {
        // SAFETY: We don't store this instance of `UnsafeBumpRefStr` inside our state.
        //         We just use it for the hashmap lookup.
        let p = UnsafeBumpRefStr(val as *const str);
        if let Some((entry, _)) = self.map.borrow().get_key_value(&p) {
            let interned = unsafe {
                // SAFETY: We only store bump allocator references inside the inner map.
                &*entry.0
            };
            return Interned(interned, self.id);
        }
        self.intern_slow(val)
    }

    #[cold]
    fn intern_slow<'a>(&'a self, val: &str) -> Interned<'a, 'g> {
        let interned = self.arena.alloc_str(val);
        let prev = self
            .map
            .borrow_mut()
            .insert(UnsafeBumpRefStr(interned as *const str), ());
        assert!(prev.is_none());
        Interned(interned, self.id)
    }

    pub fn typed_interner<'a, K: Internable>(&'a mut self) -> TypedInterner<'a, 'g, K> {
        TypedInterner {
            inner: self,
            map: RefCell::new(HashMap::default()),
            _borrow: PhantomData,
        }
    }
}

pub struct TypedInterner<'a, 'g, K> {
    inner: &'a Interner<'g>,
    map: RefCell<HashMap<K, *const str>>,
    _borrow: PhantomData<&'a mut Interner<'g>>,
}

unsafe impl<'a, 'g, K: Internable> Send for TypedInterner<'a, 'g, K> {}

impl<'a, 'g, K: Internable> TypedInterner<'a, 'g, K> {
    #[inline]
    pub fn intern(&self, val: K) -> Interned<'a, 'g> {
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
    pub fn intern_str(&self, val: &str) -> Interned<'a, 'g> {
        self.inner.intern(val)
    }

    #[cold]
    fn intern_slow(&self, vacant: VacantEntry<K, *const str>, val: K) -> Interned<'a, 'g> {
        let interned = val.intern(&self.inner.arena);
        let interned_ptr = interned as *const str;
        vacant.insert(interned_ptr);
        let prev = self
            .inner
            .map
            .borrow_mut()
            .insert(UnsafeBumpRefStr(interned_ptr), ());
        assert!(prev.is_none());
        Interned(interned, self.inner.id)
    }
}

pub trait OptionInternExt: private::Sealed {
    fn intern_in<'t, 'g>(&self, interner: &'t Interner<'g>) -> Option<Interned<'t, 'g>>;
}

impl<'a> OptionInternExt for Option<&'a str> {
    #[inline]
    fn intern_in<'t, 'g>(&self, interner: &'t Interner<'g>) -> Option<Interned<'t, 'g>> {
        self.map(|val| interner.intern(val))
    }
}

impl OptionInternExt for Option<String> {
    #[inline]
    fn intern_in<'t, 'g>(&self, interner: &'t Interner<'g>) -> Option<Interned<'t, 'g>> {
        self.as_deref().map(|val| interner.intern(val))
    }
}

pub trait OptionTypedInternExt<I>: private::Sealed
where
    I: Internable,
{
    fn intern_in<'t, 'g>(self, interner: &'t TypedInterner<'t, 'g, I>) -> Option<Interned<'t, 'g>>;
}

impl<T: Internable> OptionTypedInternExt<T> for Option<T> {
    #[inline]
    fn intern_in<'t, 'g>(self, interner: &'t TypedInterner<'t, 'g, T>) -> Option<Interned<'t, 'g>> {
        self.map(|val| interner.intern(val))
    }
}

impl<'a, T: Internable> OptionTypedInternExt<T> for Option<&'a String> {
    #[inline]
    fn intern_in<'t, 'g>(self, interner: &'t TypedInterner<'t, 'g, T>) -> Option<Interned<'t, 'g>> {
        self.map(|val| interner.intern_str(val))
    }
}

impl<'a, T: Internable> OptionTypedInternExt<T> for Option<&'a str> {
    #[inline]
    fn intern_in<'t, 'g>(self, interner: &'t TypedInterner<'t, 'g, T>) -> Option<Interned<'t, 'g>> {
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
        let $name = Interner::new(guard);
    };
    (mut $name:ident) => {
        $crate::internal::generativity::make_guard!(guard);
        let mut $name = Interner::new(guard);
    };
}

#[cfg(test)]
mod tests {
    use super::{Interned, Interner};

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
}
