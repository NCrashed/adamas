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
