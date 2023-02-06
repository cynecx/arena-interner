use arena_interner::{make_interner, Interned};

fn unify2<'a, 'b, 'c>(a: Interned<'a, 'c>, b: Interned<'b, 'c>) {
    assert_eq!(a, b);
}

fn main() {
    make_interner!(interner1);
    make_interner!(interner2);

    let a = interner1.intern("hello");
    let b = interner2.intern("hello");

    unify2(a, b);
}
