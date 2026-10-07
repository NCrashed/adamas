# The driver: `adamas` commands (adamas-cli).
#
# A literal brace is written in Fluent as {"{"} and {"}"}.

cli-fmt-1 = not canonical
cli-fmt-2 = reformatted
cli-cannot-create = could not create { $path }
cli-cannot-write = could not write { $path }
cli-cannot-read = could not read { $path }
cli-cannot-read-dir = could not read directory { $path }
cli-cannot-start = could not start { $path }
cli-specialisation = { $name }: specialisation failed: { $why }
cli-built = { $name }: built into { $path }
cli-reached-from = refusal in `{ $failed }`, reached from `{ $short }`
cli-in-definition = in definition `{ $name }`
cli-fetching = { $name }: fetching { $rev }
cli-relocked = { $file }: updated
cli-no-signature = { $name }: the pass returned no signature
cli-unknown-definition = definition `{ $name }` not found
cli-postulate = `{ $name }` has no body: a postulate cannot be evaluated
cli-unit-constructor = unit `{ $unit }` has no constructor
cli-doc-file = File `{ $name }`
cli-doc-module = Module `{ $path }`
cli-doc-empty = No documented names.
cli-fmt-refused = not formatted: { $refusal }
cli-fmt-summary = { $seen ->
    [one] { $seen } file
   *[other] { $seen } files
}, { $verb } { $changed }, { $refused ->
    [one] { $refused } refusal
   *[other] { $refused } refusals
}
cli-checked-files = { $name }: checked, { $files ->
    [one] { $files } file
   *[other] { $files } files
}, { $declarations ->
    [one] { $declarations } declaration
   *[other] { $declarations } declarations
}
cli-checked = { $name }: checked, { $declarations ->
    [one] { $declarations } declaration
   *[other] { $declarations } declarations
}
cli-unknown-name = name `{ $name }` is unknown to the signature
cli-not-empty = directory { $path } is not empty
cli-created = { $name }: created in { $path }
cli-no-package-name = no package name can be derived from path { $path }: give it with `--name`
cli-bad-package-name = `{ $name }` is not a valid package name: letters, digits, `_` and `-`; give another with `--name`
cli-test-not-a-project = { $path }: this is not a project, and tests live in a project module (`[package] test`)
cli-test-no-module = there is no test module: expected { $path }; `[package] test` sets the module name
cli-test-failed = { $name }: FAILED - { $why }
cli-test-summary = { $name }: { $tests ->
    [one] { $tests } test
   *[other] { $tests } tests
}, { $failed } failed
cli-test-not-bool = `{ $name }` is named as a test, but is not declared `Bool`; a test is a definition named `{ $prefix }…` of type `Bool`
cli-test-none = there are no tests; a test is a definition named `{ $prefix }…` of type `Bool`
cli-test-answer = expected `{ $expected }`, got `{ $found }`
cli-help-about = Adamas compiler driver
cli-help-value-name = NAME
cli-help-new = Create a project: manifest, entry and tests
cli-help-new-path = Directory for the project. Created if missing
cli-help-new-name = Package name. Defaults to the last path segment
cli-help-check = Parse, elaborate and type-check a source
cli-help-check-path = Path to an `.adamas` file, a project directory or its `adamas.toml`
cli-help-check-type = Print the type of a name instead of counting declarations. Repeatable
cli-help-build = Build the program into an executable
cli-help-build-path = Path to a project, its `adamas.toml` or an `.adamas` file
cli-help-build-backend = How to get from IR to an object file
cli-help-run = Build and run
cli-help-run-path = Path to a project, its `adamas.toml` or an `.adamas` file
cli-help-run-backend = How to get from IR to an object file
cli-help-fmt = Bring sources to canonical form
cli-help-fmt-path = An `.adamas` file or a directory: then the whole tree below it is formatted
cli-help-fmt-check = Do not write; name the files that would change
cli-help-doc = Print documentation of the externally visible interface
cli-help-doc-path = Path to an `.adamas` file, a project directory or its `adamas.toml`
cli-help-test = Run the project's tests
cli-help-test-path = Path to a project or its `adamas.toml`
cli-help-eval = Check and evaluate a definition with the machine
cli-help-eval-path = Path to an `.adamas` file, a project directory or its `adamas.toml`
cli-help-eval-name = What to evaluate. Defaults to `main`
cli-help-eval-full = Print the result in full, without cutting at depth
