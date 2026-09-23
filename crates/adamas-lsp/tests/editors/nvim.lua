-- Драйвер прогона Neovim. Запускается `crates/adamas-lsp/tests/editors.rs`.
--
-- Печатает строки `КЛЮЧ=значение`; разбирает их и сверяет с записанными руками
-- числами вызывающий тест. Сам ничего не утверждает: утверждение, живущее в
-- драйвере, легко сделать зелёным, не заметив.
--
-- Колонки Neovim отдаёт **в байтах**: `vim.diagnostic` хранит `col`/`end_col`
-- байтовыми смещениями в строке, а перевод из кодовых единиц протокола делает
-- сам, своей реализацией. Отсюда и ценность этого свидетеля - он замыкает
-- перевод чужим кодом, а не нашим.

local function say(key, value)
  io.stdout:write(key .. '=' .. tostring(value) .. '\n')
end

local function expect(name)
  local value = os.getenv(name)
  if not value or value == '' then
    error('окружение без ' .. name)
  end
  return value
end

local server = expect('ADAMAS_LSP_BIN')
local fixture = expect('ADAMAS_FIXTURE')
local forced = os.getenv('ADAMAS_FORCE_ENCODING')

-- Автокоманда группы `adamas` есть ровно тогда, когда загрузился
-- `editors/nvim/plugin/adamas.lua`. Без этой строки прогон был бы зелен и на
-- пустом runtimepath - проверял бы драйвер, а не плагин.
local plugged = vim.fn.exists('#adamas#FileType') == 1
say('PLUGIN', plugged)

if forced then
  -- Ветка мимо плагина, и запускает её тест, не добавляя каталог плагина в
  -- runtimepath. Смысл ветки - объявить клиентом одну кодировку: Neovim по
  -- умолчанию просит UTF-8 (первой в своём списке), а проверить надо и UTF-16,
  -- умолчание протокола.
  vim.cmd.edit(fixture)
  local caps = vim.lsp.protocol.make_client_capabilities()
  caps.general.positionEncodings = { forced }
  vim.lsp.start({
    name = 'adamas',
    cmd = { server },
    capabilities = caps,
    root_dir = vim.fn.getcwd(),
  })
else
  vim.g.adamas_lsp_cmd = { server }
  vim.cmd.edit(fixture)
end

say('FT', vim.bo.filetype)

local function wait_for(predicate)
  return vim.wait(30000, predicate, 50)
end

say('WAIT', wait_for(function()
  return #vim.diagnostic.get(0) > 0
end))

local clients = vim.lsp.get_clients({ bufnr = 0 })
say('CLIENTS', #clients)
for _, client in ipairs(clients) do
  say('CLIENT', client.name)
  say('ENCODING', client.offset_encoding)
end

local found = vim.diagnostic.get(0)
say('COUNT', #found)
for _, d in ipairs(found) do
  local line = vim.api.nvim_buf_get_lines(0, d.lnum, d.lnum + 1, true)[1]
  say('DIAG', vim.json.encode({
    line = d.lnum,
    start = d.col,
    ['end'] = d.end_col,
    severity = d.severity,
    source = d.source,
    message = d.message,
    -- Текст **под подчёркиванием**, нарезанный самим редактором по тем
    -- колонкам, которые он посчитал. Съехавший перевод режет не то слово, и
    -- видно это сразу.
    underlined = line:sub(d.col + 1, d.end_col),
  }))
end

-- Круг «правка -> диагностика»: убираем лишний аргумент и ждём, пока
-- подчёркивание погаснет. Без этого прогон проверял бы только `didOpen`.
local text = vim.api.nvim_buf_get_lines(0, 0, -1, true)
text[#text] = text[#text]:gsub('Succ Zero Zero', 'Succ Zero')
vim.api.nvim_buf_set_lines(0, 0, -1, true, text)
say('EDITED', text[#text])
say('CLEARED', wait_for(function()
  return #vim.diagnostic.get(0) == 0
end))

-- Подсказки §5.1 на **починенном** буфере: пока он не проверяется, вердикта
-- нет и показывать нечего. Спрашиваются они у `vim.lsp.inlay_hint`, то есть у
-- того самого механизма, которым Neovim их рисует; включает его плагин
-- (`editors/nvim`), и в ветке без плагина их поэтому не будет вовсе.
local hint = vim.lsp.inlay_hint
say('INLAY_API', hint ~= nil and hint.get ~= nil)
if hint and hint.get then
  -- `ADAMAS_FORCE_INLAY` включает подсказки **мимо плагина** - тем же вызовом,
  -- каким их включает он. Нужно это ветке с заданной кодировкой: плагина там
  -- нет по построению, а UTF-16 проверить надо.
  local forced_inlay = os.getenv('ADAMAS_FORCE_INLAY')
  if forced_inlay and hint.enable then
    hint.enable(true, { bufnr = 0 })
  end
  -- Ждать есть смысл только там, где подсказки должны прийти: в ветке без
  -- включения ожидание вырождалось бы в тридцать секунд простоя на прогон.
  if plugged or forced_inlay then
    wait_for(function()
      return #hint.get({ bufnr = 0 }) > 0
    end)
  end
  local shown = hint.get({ bufnr = 0 })
  say('INLAY_COUNT', #shown)
  for _, item in ipairs(shown) do
    local position = item.inlay_hint.position
    local row = vim.api.nvim_buf_get_lines(0, position.line, position.line + 1, true)[1]
    local label = item.inlay_hint.label
    if type(label) == 'table' then
      local parts = {}
      for _, piece in ipairs(label) do
        parts[#parts + 1] = piece.value
      end
      label = table.concat(parts)
    end
    -- `character` здесь уже **байтовая** колонка: Neovim переводит позицию
    -- протокола своей реализацией, когда принимает подсказку, и наружу отдаёт
    -- готовое. Отсюда и ценность числа - счёт чужой, не наш.
    say('INLAY', vim.json.encode({
      line = position.line,
      column = position.character,
      label = label,
      -- Текст **от места подсказки до конца строки**, нарезанный редактором по
      -- своему счёту: подсказка, уехавшая на байты, режет не то слово.
      after = row:sub(position.character + 1),
    }))
  end
end

vim.cmd('qa!')
