use arena_interner::{make_interner, Interned};

fn unify<'a, 'b>(a: Interned<'a, 'b>, b: Interned<'a, 'b>) {
    assert_eq!(a, b);
}

fn main() {
    make_interner!(interner1);
    make_interner!(interner2);

    let a = interner1.intern("hello");
    let b = interner2.intern("hello");

    unify(a, b);
}
