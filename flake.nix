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

        # Редакторы Фазы 9 (§9, волна 1, трек C). В dev-shell их не было вовсе,
        # и заводятся они тем же порядком, что LLVM Фазы 7: инструмент, которым
        # проверяется утверждение, приезжает флейком, а не «есть у меня в
        # системе».
        #
        # Обе стороны гоняются **headless**, и обе - целым редактором, а не его
        # подобием: nvim пишет диагностику в буфер сам, VSCodium поднимает
        # расширение в настоящем extension host'е. Цена замерена докачкой
        # поверх прежнего shell'а: neovim с node вместе - 74,8 MiB, vscodium -
        # 421 MiB (1,3 GiB распакованного), vsce - 28 MiB.
        #
        # VSCodium, а не `vscode`: сборка та же самая, API расширений то же
        # самое, а unfree-лицензии нет - иначе флейк требовал бы
        # `allowUnfree` от каждого, кто его открывает.
        editorNvim = pkgs.neovim;
        editorVscode = pkgs.vscodium;

        # `node` нужен не сборке расширения (её нет: расширение - обычный JS без
        # шага компиляции), а `npm ci`, которым приезжает `vscode-languageclient`.
        nodejs = pkgs.nodejs;

        # Упаковка `.vsix`. Из nixpkgs, а не из `devDependencies`: тот же `vsce`
        # через npm - 239 пакетов и 134 MiB с нативной сборкой keytar, здесь -
        # 28 MiB готовым замыканием.
        vsce = pkgs.vsce;

        # Пакетный менеджер Фазы 9 (§7.3, волна 2, трек C). `adamas-pkg` зовёт
        # системный `git` - выбор назван в `crates/adamas-pkg/src/fetch.rs`, -
        # и до сих пор он приезжал из системы: в `nativeBuildInputs` его не
        # было ни одного, а тесты достачи его требуют. Переменной, как у LLVM и
        # редакторов, не заводится намеренно: `git` зовёт **инструмент
        # пользователя**, а не свидетель, и брать его он обязан оттуда же,
        # откуда возьмёт у всякого другого - из `PATH`.
        git = pkgs.git;
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
            editorNvim
            nodejs
            vsce
            git
            # Экранный сервер для VSCodium: Electron без дисплея не поднимается,
            # а `xvfb-run` даёт его на время одного прогона.
            pkgs.xvfb-run
          ];

          # Каталогами, а не именами: цепочка инструментов обязана быть одной
          # версии целиком, иначе стадии конвейера читали бы разный IR. Обе
          # переменные читает `adamas-codegen::llvm`.
          #
          # clang - **путём**, а не через `nativeBuildInputs`, и это не стиль:
          # обёртка clang в nixpkgs кладёт в `bin` ещё и `cc`, а `cc`-крейт
          # берёт компилятор из `PATH`. Попади он туда - рантайм и порождённый C
          # собирались бы clang'ом вместо gcc, молча и во всех замерах разом.
          #
          # Редакторы - тоже путями, и по своим причинам.
          #
          # У VS Code переменных две, и это не дублирование - это два разных
          # бинаря с разными обязанностями.
          #
          # `ADAMAS_VSCODE` - **Electron**. Он ждёт конца
          # `--extensionTestsPath` и отдаёт его код возврата. CLI-обёртка
          # `bin/codium` на том же аргументе возвращается сразу: прогон с ней
          # зелен за секунду и не проверяет ничего (измерено: `EXIT=0
          # ELAPSED=1s`, ни строчки вывода сюиты). Обёртка окружения nixpkgs
          # при этом не нужна - голый Electron под Xvfb поднимается и без неё.
          #
          # `ADAMAS_VSCODE_CLI` - та самая обёртка, и она нужна ровно на
          # `--install-extension`: это работа CLI, и Electron её не делает.
          # Измерено: Electron с `--install-extension` открывает окно и висит
          # (девять минут до убийства), обёртка ставит `.vsix` меньше чем за
          # секунду и дисплея не просит.
          #
          # Значение `absent` у любой из четырёх - объявленное отсутствие
          # инструмента (правило `ADAMAS_LLVM=absent`, `.github/workflows/ci.yml`).
          # Переменная **не заданная** - отказ, а не пропуск.
          env = {
            ADAMAS_LLVM_BIN = "${llvmCurrent}/bin";
            ADAMAS_LLVM_MIN_BIN = "${llvmMinimum}/bin";
            ADAMAS_CLANG = "${clangCurrent}/bin/clang";
            ADAMAS_NVIM = "${editorNvim}/bin/nvim";
            ADAMAS_VSCODE = "${editorVscode}/lib/vscode/codium";
            ADAMAS_VSCODE_CLI = "${editorVscode}/bin/codium";
            ADAMAS_VSCE = "${vsce}/bin/vsce";
          };

          # Зависимости расширения ставятся npm'ом, а не Nix'ом, и причина
          # внешняя: CI Nix не поднимает, там всё равно будет `npm ci`. Второй
          # способ поставить те же восемь пакетов не окупается - пин у них один
          # и тот же, `editors/vscode/package-lock.json`.
          shellHook = ''
            if [ -f editors/vscode/package-lock.json ] && [ ! -d editors/vscode/node_modules ]; then
              echo "adamas: ставлю зависимости расширения VS Code (npm ci)..." >&2
              (cd editors/vscode && npm ci --no-audit --no-fund) || \
                echo "adamas: npm ci не прошёл; свидетель VS Code скажет об этом внятно" >&2
            fi
          '';
        };

        # nixfmt-tree, а не голый nixfmt: последний на `nix fmt` без аргументов
        # читает пустой stdin и падает, а на директории ругается deprecation'ом.
        formatter = pkgs.nixfmt-tree;
      }
    );
}
