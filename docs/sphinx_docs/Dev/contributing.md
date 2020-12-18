# Contributing

## Pull Request Guidelines

External contributions to Alt-Ergo may be proposed using git's standard pull request mechanism from your `base` branch to our `target` one ( `next` by default).
The following terms apply to all such contributions:

* We require all pull requests to pass :

	* Our non regression suite, you can run `make non-regression` to check if your changes affect the performance and answers of Alt-Ergo.

	* Our style checking, every lines should length 80 columns maximum and should be indent with ocp-indent.
	  We strongly recommand to use the following command line so the indent and style checking will be done automatically when commiting.

	```cp rsc/extra/pre-commit-git-hook .git/hooks/pre-commit```

* Pull request should be rebased and up to date from the `base` branch to be merged.

* All commits will be squashed into one when merged into the `base` branch. A PR with only one commit is appreciated if the modification are minimal. Else, we ask for a clean commit history with relevant messages since it facilitates the review.

## Legal Guidelines

In addition to agreeing to the terms of the Alt-Ergo's [License], we ask our contributors to sign the [Contributor License Agreement (CLA)].

[License]: ../About/license.md
[Contributor License Agreement (CLA)]: https://www.ocamlpro.com/files/CLA-OCamlPro-corporate.txt