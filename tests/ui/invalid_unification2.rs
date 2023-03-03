use arena_interner::{make_interner, Interned};

fn unify2<'a, 'b, 'c>(a: Interned<'a, 'c, str>, b: Interned<'b, 'c, str>) {
    assert_eq!(a, b);
}

fn main() {
    make_interner!(interner1: str);
    make_interner!(interner2: str);

    let a = interner1.intern("hello");
    let b = interner2.intern("hello");

    unify2(a, b);
}
