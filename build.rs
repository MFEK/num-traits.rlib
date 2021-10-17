extern crate autocfg;
extern crate rustc_version;

use std::env;

fn main() {
    let ac = autocfg::new();
    if probe("fn main() { 0i128; }") {
        println!("cargo:rustc-cfg=has_i128");
    } else if env::var_os("CARGO_FEATURE_I128").is_some() {
        panic!("i128 support was not detected!");
    }

    match rustc_version::version_meta() {
        Ok(ref meta) if meta.semver.major >= 1 && meta.semver.minor >= 32 => {
            println!("cargo:rustc-cfg=int_to_from_bytes");
        }
        Ok(ref meta)
            if env::var_os("CARGO_FEATURE_INT_TO_FROM_BYTES").is_some()
                && meta.channel == rustc_version::Channel::Stable =>
        {
            panic!("`int_to_from_bytes` support was not stabilizations!");
        }
        _ => {}
    }
}

    // If the "i128" feature is explicity requested, don't bother probing for it.
    // It will still cause a build error if that was set improperly.
    if env::var_os("CARGO_FEATURE_I128").is_some() || ac.probe_type("i128") {
        autocfg::emit("has_i128");
    }

    ac.emit_expression_cfg(
        "unsafe { 1f64.to_int_unchecked::<i32>() }",
        "has_to_int_unchecked",
    );

    ac.emit_expression_cfg("1u32.reverse_bits()", "has_reverse_bits");
    ac.emit_expression_cfg("1u32.trailing_ones()", "has_leading_trailing_ones");

    autocfg::rerun_path("build.rs");
}
