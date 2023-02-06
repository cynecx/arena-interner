use arena_interner::make_interner;

fn main() {
    make_interner!(interner1);
    make_interner!(interner2);

    let a = interner1.intern("hello");
    let b = interner2.intern("hello");

    assert_eq!(a, b);
}
