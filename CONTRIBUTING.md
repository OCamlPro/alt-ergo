# Guide to contributing to Alt-Ergo

## Foreword

This guide is intended to as best as possible reflect the current state of the processes and tools used in the development of Alt-Ergo. It may get stale or outdated from time to time: if you notice anything incorrect or that otherwise no longer applies in this guide, please signal it in an issue or fix it in a pull request. If you find it unclear or imprecise on certain points, please open an issue as well so that we can try to make it better.

## Pull Request Guidelines

External contributions to Alt-Ergo may be proposed using git's standard pull request mechanism from your `base` branch to our `target` one ( `next` by default).
The following terms apply to all such contributions:

* We require all pull requests to pass :

	* Our non regression suite, you can run `make runtest` to check if your changes affect the performance and answers of Alt-Ergo.

	* Our style checking, every lines should length 80 columns maximum and should be indent with ocp-indent.
	  We strongly recommand to use the following command line so the indent and style checking will be done automatically when commiting.

	```cp rsc/extra/pre-commit-git-hook .git/hooks/pre-commit```

* Pull request should be rebased and up to date from the `base` branch to be merged.

* All commits will be squashed into one when merged into the `base` branch. A PR with only one commit is appreciated if the modification are minimal. Else, we ask for a clean commit history with relevant messages since it facilitates the review.

## Legal Guidelines

In addition to agreeing to the terms of the Alt-Ergo's [License], we ask our contributors to sign the [Contributor License Agreement (CLA)].

[License]: ../About/license
[Contributor License Agreement (CLA)]: https://www.ocamlpro.com/files/CLA-OCamlPro-corporate.txt

## Develop with Nix

If you are using nix, you can get a development shell for Alt-Ergo using:

```shell
$ nix-shell
```

To build and run a development version of alt-ergo you can use (this requires
the [experimental `nix` command](https://nixos.wiki/wiki/Nix_command)):

```shell
$ nix run -f . alt-ergo
```

Or directly from GitHub:

```shell
$ nix run -f https://github.com/OCamlPro/alt-ergo/archive/master.tar.gz#alt-ergo alt-ergo
```

## Release Process

Alt-Ergo releases do not have a fixed schedule and are made based on features. We try to maintain the main branch (`next`) of the repository as stable as possible, and cut a release from there when an important feature is complete. We also make point release to fix important bugs.

Once we decide to make a release, a release manager (RM) is nominated amongst the core developers. The release manager creates a new `X.Y.Z` branch for the release from the current `next`, marking the beginning of a feature freeze for the release: new features may continue to get merged on `next`, but will not be included in that release. **The RM is the only person allowed to merge PRs or otherwise make changes on the release branch.**

Changes are never introduced directly into the release branch (with some exceptions below): after branching, any change that goes into the release branch must be backported from a corresponding change on `next`. It must be mentioned in the pull request that there is a desire to backport the change to the current release. It is then up to the RM to decide whether to include that change in the release or not, and they must only do so *after the original change has been merged into `next`*. This ensures that there are never features that make it to a release branch but not to `next`.

Specific changes that are only relevant for a specific release can result in a PR targeting the release branch directly. In this case, only the RM is allowed to merge the PR onto the release branch, even if they are the PR's author. Such PRs are typically either bug fixes for features that are removed or significantly changed on `next` (very rare!), and PRs to change the version number in preparation for the release.

The rest of this section is intended for the release manager, and describes the tasks associated with a release.

### Make a PR for the release

This is the first step, and should be taken only once `next` is feature complete for the release to minimise churn. The RM makes a PR on `next` to initiate the release. The PR must introduce a new section in `CHANGES.md` with the new version number.

This PR should ideally only modify `CHANGES.md`, and involves moving items from the `unreleased` section to a new section including the new release number (but no release date yet).

Once the PR is merged, the RM creates a new branch called `X.Y.x`; for instance, the release branch for version `2.5.0` will be called `v2.5.x`. The branch must target the merge commit.

### Update documentation

The merging of the release PR marks the definitive set of features that are included in the release. The RM makes sure that the relevant features are properly documented; changes to the documentation must be done on the `next` branch then backported to the release branch (the RM is encouraged to collaborate with the developer of a specific feature for help in documenting it). This includes updating the release notes appropriately.

### Run benchmarks

Once the release branch has been confirmed, the RM runs some benchmarks to compare the state of the release branch against the last released version. These benchmarks are stored on an internal OCamlPro machine. The following benchmarks should be run (note: the Zulip bot can help):

 - ae-format benchmarks (internal dataset in the native format)
 - ae-format-fpa benchmarks (internal dataset in the native format, using the floating-point theories)
 - benchtop-tests benchmarks (smtcomp subset)

If regressions are found, they must be first confirmed by checking that they are still present in a different environment, to ensure they are not spurious regressions due to the weak table. The simplest way to do it is to compile with a different version of OCaml (this is what the Zulip bot does). See https://github.com/OCamlPro/alt-ergo/issues/563 for details on the weak table issue.

Confirmed regressions must be investigated to understand their cause. For each cause of regressions, an issue (the granularity of the issues are at the discretion of the RM) must be created to document the cause of the regression. The RM then decides whether the regression must be fixed for the release or not (this is a case-by-case process, but as a general guideline, regressions should be fixed unless the source of the regression is also the source of at least a comparable amount of improvements).

Fixes for the regressions must be made in PRs to the `next` branch that are then back-ported to the release branch, as described above.

### Prepare an announcement

Once the release is ready and all the tests and benchmarks pass, the last step before making the release proper is to write an announcement for the release. The announcement will be posted on the OCamlPro blog, on the mailing list, and on the OCaml Discourse. It should highlight the new features and major bug fixes in the release, and is written by the RM in collaboration with the other developers.

### Make the release

The release is made using `dune-release`, and follows standard procedure for the tool. Check the output of `dune-release help release`, but essentially:

 - `dune-release check` (performs basic check)
 - `dune-release tag vX.Y.Z` (replace `X`, `Y` and `Z` as appropriate; this creates a git tag -- you may add alphas, betas, or rc)
 - `dune-release distrib` (this creates the distribution archive)
 - `dune-release publish distrib` (this is irreversible: it publishes the release on GitHub)
 - `dune-release opam pkg` (this an archive with the opam stuff)
 - `dune-release opam submit` (this opens a MR on the opam repository)
