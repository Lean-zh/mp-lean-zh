# Lean 4 元编程

Authors: Arthur Paulino, Damiano Testa, Edward Ayers, Evgenia Karunus, Henrik Böving, Jannis Limperg, Siddhartha Gadgil, Siddharth Bhat

译者：[subfish_zhou](https://github.com/subfish-zhou)

* The textbook in html format is [here](https://leanprover-community.github.io/lean4-metaprogramming-book/).
* 中文版网页链接在[这里](https://www.leanprover.cn/mp-lean-zh/)

* A PDF is [available here for download](../../releases/download/latest/Metaprogramming.in.Lean.4.pdf) (中文版PDF会乱码).

## Contributing

The markdown files are generated automatically via [mdgen](https://github.com/Seasawher/mdgen).
Thus, if you're going to write or fix content for the book, please do so in the original Lean files inside the [lean](lean) directory.

**Important**: since `mdgen` is so simple, please avoid using comment sections
in Lean code blocks with `/- ... -/`. If you want to insert commentaries, do so
with double dashes `--`.

### Building the markdown files

This is not required, but if you want to build the markdown files, you can do so by running `lake run mdbuild`.
