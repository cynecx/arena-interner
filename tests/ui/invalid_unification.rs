use arena_interner::{make_interner, Interned};

fn unify<'a, 'b>(a: Interned<'a, 'b, str>, b: Interned<'a, 'b, str>) {
    assert_eq!(a, b);
}

fn main() {
    make_interner!(interner1: str);
    make_interner!(interner2: str);

    let a = interner1.intern("hello");
    let b = interner2.intern("hello");

    unify(a, b);
}
