//! End-to-end smoke-тест драйвера: процесс запускается, читает файл, отвечает.
//!
//! Проверяет не семантику (её ещё нет), а что цепочка
//! «argv -> clap -> adamas-core -> stdout» собрана и работает.

use std::process::Command;

fn adamas() -> Command {
    Command::new(env!("CARGO_BIN_EXE_adamas"))
}

#[test]
fn reports_source_stats() {
    // CARGO_TARGET_TMPDIR уникален для пакета и чистится вместе с target/.
    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("check-smoke");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("sample.adamas");
    std::fs::write(&path, "id : (0 a : Type) -> a -> a\nid x = x\n").unwrap();

    let output = adamas().arg("check").arg(&path).output().unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();

    assert!(
        output.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(stdout.contains("37 bytes"), "unexpected stdout: {stdout}");
    assert!(stdout.contains("3 lines"), "unexpected stdout: {stdout}");
}

#[test]
fn missing_file_fails_without_panic() {
    let output = adamas()
        .arg("check")
        .arg("does-not-exist.adamas")
        .output()
        .unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();

    assert!(!output.status.success());
    assert!(!stderr.contains("panicked"), "driver panicked: {stderr}");
    assert!(
        stderr.contains("does-not-exist.adamas"),
        "unhelpful error: {stderr}"
    );
}
