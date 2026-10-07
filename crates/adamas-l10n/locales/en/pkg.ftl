# Packages: manifest, lockfile, git dependencies (adamas-pkg).
#
# A literal brace is written in Fluent as {"{"} and {"}"}.

pkg-no-manifest = manifest not found: { $v0 }
pkg-read = could not read { $path }: { $source }
pkg-write = could not write { $path }: { $source }
pkg-syntax = { $path }: { $message }
pkg-shape = { $path }: { $message }
pkg-git = git { $command }: { $message }
pkg-fetch-1 = the checkout was not renamed
pkg-lock-1 = no `version` field
pkg-lock-2 = `package` is not an array of tables
pkg-lock-3 = an element of `package` is not a table
pkg-manifest-1 = no `[package]` table
pkg-manifest-2 = `package` is not a table
pkg-manifest-3 = `[package]` has no `name`
pkg-manifest-4 = `dependencies` is not a table
pkg-manifest-5 = `link` is not a table
pkg-git-not-started = did not start: { $source }
pkg-git-not-found = in repository { $repository }: { $asked } not found
pkg-lock-version = format version { $version }, the tool understands { $known }: delete the file, it will be created anew
pkg-lock-missing-key = `[[package]]` has no `{ $key }`
pkg-manifest-not-string = `{ $section }.{ $key }` is not a string
pkg-manifest-not-strings = `{ $section }.{ $key }` is not a list of strings
pkg-manifest-library = `link.libraries` = `{ $written }` is not a library name: it is written as for `-l`, without `lib` and without an extension
pkg-manifest-dependency-table = `dependencies.{ $prefix }` is not a table: a dependency is written `{"{"} git = "…", tag = "…" {"}"}`
pkg-manifest-no-git = `[dependencies.{ $prefix }]` has no `git`; a compound prefix is written in quotes: `"{ $prefix }.Something" = {"{"} git = … {"}"}`
pkg-manifest-no-version = `[dependencies.{ $prefix }]` has neither `rev` nor `tag` (§7.3: a git URL plus a commit or a tag)
pkg-manifest-rev-and-tag = `[dependencies.{ $prefix }]` has both `rev` and `tag`: choose one
pkg-manifest-module-path = `{ $field }` = `{ $written }` is not a module path: segments separated by dots, each of letters, digits, `_` and `'`
pkg-manifest-file-name = `{ $field }` = `{ $written }` is not a file name: letters, digits, `_` and `-`
pkg-manifest-escapes = `{ $field }` = `{ $written }` leads outside the manifest directory
