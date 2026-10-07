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
