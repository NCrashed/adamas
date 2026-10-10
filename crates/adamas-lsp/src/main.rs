//! Запуск LSP-сервера Adamas на stdin/stdout (§7.2).
//!
//! Тонкий: всё, что делает сервер, живёт в библиотеке - иначе прогон не мог бы
//! позвать его иначе как процессом, а проверять надо и то и другое.

fn main() -> std::process::ExitCode {
    // Сервер - в потоке со своим стеком, как и драйвер (§10 вопрос 187).
    match adamas_elab::with_stack(adamas_lsp::run) {
        Ok(()) => std::process::ExitCode::SUCCESS,
        Err(error) => {
            // stderr, а не stdout: по stdout идёт протокол, и посторонний
            // байт в нём сбивает рамку сообщения у клиента.
            eprintln!("adamas-lsp: {error}");
            std::process::ExitCode::FAILURE
        }
    }
}
