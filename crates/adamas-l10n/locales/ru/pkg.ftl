# Пакеты: манифест, лок-файл, git-зависимости (adamas-pkg).
#
# Литеральная фигурная скобка пишется во Fluent как {"{"} и {"}"}.

pkg-no-manifest = манифест не найден: { $v0 }
pkg-read = не удалось прочитать { $path }: { $source }
pkg-write = не удалось записать { $path }: { $source }
pkg-syntax = { $path }: { $message }
pkg-shape = { $path }: { $message }
pkg-git = git { $command }: { $message }
pkg-fetch-1 = чекаут не переименовался
pkg-lock-1 = нет поля `version`
pkg-lock-2 = `package` - не массив таблиц
pkg-lock-3 = элемент `package` - не таблица
pkg-manifest-1 = нет таблицы `[package]`
pkg-manifest-2 = `package` - не таблица
pkg-manifest-3 = в `[package]` нет `name`
pkg-manifest-4 = `dependencies` - не таблица
pkg-manifest-5 = `link` - не таблица
pkg-git-not-started = не запустился: { $source }
pkg-git-not-found = в репозитории { $repository }: не найден { $asked }
pkg-lock-version = версия формата { $version }, инструмент понимает { $known }: удалите файл, он будет создан заново
pkg-lock-missing-key = в `[[package]]` нет `{ $key }`
pkg-manifest-not-string = `{ $section }.{ $key }` - не строка
pkg-manifest-not-strings = `{ $section }.{ $key }` - не список строк
pkg-manifest-library = `link.libraries` = `{ $written }` - не имя библиотеки: пишется оно как у `-l`, без `lib` и без расширения
pkg-manifest-dependency-table = `dependencies.{ $prefix }` - не таблица: зависимость пишется `{"{"} git = "…", tag = "…" {"}"}`
pkg-manifest-no-git = в `[dependencies.{ $prefix }]` нет `git`; составной префикс пишется в кавычках: `"{ $prefix }.Что-то" = {"{"} git = … {"}"}`
pkg-manifest-no-version = в `[dependencies.{ $prefix }]` нет ни `rev`, ни `tag`: зависимость - это git URL плюс коммит или тег
pkg-manifest-rev-and-tag = в `[dependencies.{ $prefix }]` написаны и `rev`, и `tag`: выберите одно
pkg-manifest-module-path = `{ $field }` = `{ $written }` - не путь модуля: сегменты через точку, каждый из букв, цифр, `_` и `'`
pkg-manifest-file-name = `{ $field }` = `{ $written }` - не имя файла: буквы, цифры, `_` и `-`
pkg-manifest-escapes = `{ $field }` = `{ $written }` выводит за каталог манифеста
