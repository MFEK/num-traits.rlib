extern crate autocfg;

use std::env;

fn main() {
    let ac = autocfg::new();
    if ac.probe_expression("fn main() { 0i128; }") {
        println!("cargo:rustc-cfg=has_i128");
    } else if env::var_os("CARGO_FEATURE_I128").is_some() {
        panic!("i128 support was not detected!");
    }

    if ac.probe_expression(r#"
    fn main() { 
        let bytes = 0x1234567890123456u64.to_ne_bytes();

        assert_eq!(bytes, if cfg!(target_endian = "big") {
            [0x12, 0x34, 0x56, 0x78, 0x90, 0x12, 0x34, 0x56]
        } else {
            [0x56, 0x34, 0x12, 0x90, 0x78, 0x56, 0x34, 0x12]
        });
    }"#) {
        println!("cargo:rustc-cfg=int_to_from_bytes");
    }

    // If the "i128" feature is explicity requested, don't bother probing for it.
    // It will still cause a build error if that was set improperly.
    if env::var_os("CARGO_FEATURE_I128").is_some() || ac.probe_type("i128") {
        autocfg::emit("has_i128");
    }

    if env::var_os("CARGO_FEATURE_COPYSIGN").is_some() || ac.probe_expression("f32::copysign") {
        autocfg::emit("has_copysign");
    }

    ac.emit_expression_cfg(
        "unsafe { 1f64.to_int_unchecked::<i32>() }",
        "has_to_int_unchecked",
    );

    ac.emit_expression_cfg("1u32.reverse_bits()", "has_reverse_bits");
    ac.emit_expression_cfg("1u32.trailing_ones()", "has_leading_trailing_ones");
    ac.emit_expression_cfg(
        r#"
            trait TestTrait {}
            struct TestType {}
            impl const TestTrait for TestType {}
        "#,
        "has_const_trait_impl",
    );
    ac.emit_expression_cfg(
        "0x1234567890123456u64.to_ne_bytes()",
        "has_int_to_from_bytes",
    );

    ac.emit_expression_cfg("3.14f64.to_ne_bytes()", "has_float_to_from_bytes");

    autocfg::rerun_path("build.rs");
}
