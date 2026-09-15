{
  description = "Adamas — research-level functional language (QTT + algebraic effects + Perceus)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      self,
      nixpkgs,
      rust-overlay,
      flake-utils,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        overlays = [ (import rust-overlay) ];
        pkgs = import nixpkgs { inherit system overlays; };

        # Версия — из rust-toolchain.toml, тот же файл читает CI через rustup.
        rustToolchain = pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml;

        rustPlatform = pkgs.makeRustPlatform {
          cargo = rustToolchain;
          rustc = rustToolchain;
        };

        # LLVM Фазы 7 (§9). Привязка текстовая (решение 2026-09-15), поэтому
        # нужны бинари, а не библиотека: `llvm-as`, `opt`, `llc` - все три
        # лежат в `llvm`.
        llvmCurrent = pkgs.llvmPackages.llvm;

        # Минимальная поддерживаемая версия. Правило «консервативное
        # подмножество IR» проверяется прогоном на ней, а не грепом по формам:
        # тот же порядок, что у MSRV. Число продублировано в
        # `adamas-codegen::llvm::MINIMUM_MAJOR`, и совпадение двух записей
        # проверяет `crates/adamas-codegen/tests/llvm.rs`.
        llvmMinimum = pkgs.llvmPackages_18.llvm;

        # Отладчик Фазы 7 (§9, волна 1, трек E). Критерий трека - утверждение
        # про сеанс («в отладчике видно имя и значение»), и проверяется он
        # пакетным `gdb --batch`, а не чтением метаданных: узел в тексте `.ll`
        # доказывает, что он написан, и молчит о том, найдёт ли отладчик по
        # нему значение. gdb, а не lldb: скриптуется одинаково, но в nixpkgs
        # приезжает без сборки всего LLVM-стека второй раз.
        debugger = pkgs.gdb;

        # Рантайм битовым кодом (§9 Фаза 7, трек A′, вторая половина). Нужен
        # ровно тем, что `opt` не видит сквозь `adamas_dup`, пока рантайм
        # приезжает готовым объектником: `llvm-link` с `.bc` это снимает, а
        # собрать `.bc` из C нечем, кроме clang - gcc битового кода LLVM не
        # выдаёт. Версия обязана совпасть с `llvmCurrent`: `llvm-link` читает
        # битовый код своего мажора.
        clangCurrent = pkgs.llvmPackages.clang;
      in
      {
        packages.default = rustPlatform.buildRustPackage {
          pname = "adamas";
          version = "0.0.0";
          src = ./.;
          cargoLock.lockFile = ./Cargo.lock;

          meta = with pkgs.lib; {
            description = "Adamas compiler toolchain";
            homepage = "https://github.com/NCrashed/adamas";
            license = with licenses; [
              mit
              asl20
            ];
            mainProgram = "adamas";
          };
        };

        devShells.default = pkgs.mkShell {
          nativeBuildInputs = [
            rustToolchain
            pkgs.cargo-insta
            pkgs.cargo-mutants
            llvmCurrent
            debugger
          ];

          # Каталогами, а не именами: цепочка инструментов обязана быть одной
          # версии целиком, иначе стадии конвейера читали бы разный IR. Обе
          # переменные читает `adamas-codegen::llvm`.
          #
          # clang - **путём**, а не через `nativeBuildInputs`, и это не стиль:
          # обёртка clang в nixpkgs кладёт в `bin` ещё и `cc`, а `cc`-крейт
          # берёт компилятор из `PATH`. Попади он туда - рантайм и порождённый C
          # собирались бы clang'ом вместо gcc, молча и во всех замерах разом.
          env = {
            ADAMAS_LLVM_BIN = "${llvmCurrent}/bin";
            ADAMAS_LLVM_MIN_BIN = "${llvmMinimum}/bin";
            ADAMAS_CLANG = "${clangCurrent}/bin/clang";
          };
        };

        # nixfmt-tree, а не голый nixfmt: последний на `nix fmt` без аргументов
        # читает пустой stdin и падает, а на директории ругается deprecation'ом.
        formatter = pkgs.nixfmt-tree;
      }
    );
}
