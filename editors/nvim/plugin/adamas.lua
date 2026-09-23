-- Запуск `adamas-lsp` на буферах Adamas (§7.2, §9 Фаза 9).
--
-- `vim.lsp.start` в автокоманде `FileType`, а не `vim.lsp.config`/`vim.lsp.enable`:
-- второе появилось в Neovim 0.11, а первое работает с 0.8. Конфигурация
-- редактора, которая требует свежайшего редактора, - не конфигурация.
--
-- Клиент один на сеанс. `root_dir` - текущий каталог, а не каталог файла, и
-- теперь это не удобство, а необходимость: путь модуля пишется от корня
-- проекта (`import Std.Base` - это `<корень>/Std/Base.adamas`), и сервер берёт
-- корень из `rootUri` рукопожатия. Каталог файла завёл бы по серверу на каждый
-- подкаталог, и в каждом `Std.Base` искался бы не там.

local group = vim.api.nvim_create_augroup('adamas', { clear = true })

vim.api.nvim_create_autocmd('FileType', {
  group = group,
  pattern = 'adamas',
  desc = 'поднять языковой сервер Adamas',
  callback = function(args)
    -- `vim.g.adamas_lsp_cmd` - для тех, у кого бинарь не в PATH; списком, а не
    -- строкой, потому что `cmd` принимает argv.
    local cmd = vim.g.adamas_lsp_cmd or { 'adamas-lsp' }
    if vim.fn.executable(cmd[1]) == 0 then
      -- Молча не уходим: буфер без подчёркиваний выглядит так же, как буфер без
      -- ошибок, и отличить их человеку нечем.
      vim.notify(
        ('adamas: `%s` не найден; поставь его в PATH или задай vim.g.adamas_lsp_cmd')
          :format(cmd[1]),
        vim.log.levels.WARN
      )
      return
    end
    vim.lsp.start({
      name = 'adamas',
      cmd = cmd,
      root_dir = vim.fn.getcwd(),
    }, { bufnr = args.buf })
  end,
})

-- Подсказки §5.1 (куча и переиспользование ячейки) сервер отдаёт по запросу, а
-- запрашивает их Neovim только после явного включения: с 0.10 `inlayHint`
-- умолчательно выключен. VS Code рисует их сам, и разница эта не про вкус
-- редакторов - протокол оставляет показ на усмотрение клиента. Без этих строк
-- возможность существовала бы только в ответах сервера.
--
-- Включается на `LspAttach` и **только для своего клиента**: чужие серверы в том
-- же сеансе трогать нечем.
vim.api.nvim_create_autocmd('LspAttach', {
  group = group,
  desc = 'включить подсказки Adamas о куче и переиспользовании ячейки',
  callback = function(args)
    local client = vim.lsp.get_client_by_id(args.data.client_id)
    if not client or client.name ~= 'adamas' then
      return
    end
    -- API от 0.10; плагин обещает работать с 0.8, поэтому наличие проверяется,
    -- а не предполагается.
    local hint = vim.lsp.inlay_hint
    if hint and hint.enable then
      hint.enable(true, { bufnr = args.buf })
    end
  end,
})
