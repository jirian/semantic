# Owned split in Scala 3 capture checking

`src/main/scala/Split.scala` declares owned splitting as a *trusted library primitive*:

```scala
def split(consume s: Slice^, n: Int): Halves^   // two fresh, separate halves
```

Scala's separation checker (Scala 3.9.0, `-language:experimental.captureChecking`,
`-language:experimental.separationChecking`) then accepts the `process` program of the
abstract and rejects misuse. Each file in `neg/` must fail to compile; run `./check-neg.sh`:

| `neg/` file | misuse | rejected because |
| --- | --- | --- |
| `UseParentAfterSplit.scala` | write the parent after splitting it | `buf` was consumed by `split` |
| `RaceOnHalf.scala` | write one half in both branches of `par` | the branches are not separate |
| `UseAfterSend.scala` | write a half after `send` consumed it | `body` was consumed by `send` |
| `SplitBorrowed.scala` | split a parameter that is not `consume` | `buf` is borrowed |

The body of `split` bypasses the checker (`unsafeAssumeSeparate`), as Capybara's `splitAt`
does. The Lean development in the parent directory is what justifies trusting this
signature: `HasType.split` gives `split` exactly this type, and the fundamental theorem
proves it sound.

Build: `sbt compile`, `sbt run`, `./check-neg.sh`.
