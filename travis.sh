exit_if_error(){
    if [ "$?" -ne "0" ] ; then
        echo "!!! exit if error triggered !!!"
        exit 1
    fi
}

non_regression(){
    echo "=+= [travis.sh] non-regression tests ... =+="
    echo "which alt-ergo == `which alt-ergo`"
    echo "alt-ergo -version == `alt-ergo -version`"

    cd ../non-regression

    sh ./run_valid.sh "alt-ergo" "0.5" ; exit_if_error

    sh ./run_invalid.sh "alt-ergo" "0.5" ; exit_if_error

    # - make non-regression
}

local_install_dir=`pwd`/___local

git_repo=`pwd`

## dummy switch
opam sw DUMMY --alias system
eval `opam config env`
opam update

# in travis, 'system' compiler is currently < 4.04.0

for ocaml_version in 4.06.0 # 4.05.0 4.04.0
do
    echo "=+= [travis.sh] testing with OCaml version '$ocaml_version' =+="

    opam sw remove $ocaml_version # failure if does not exist accepted !
    opam sw $ocaml_version ; exit_if_error
    eval `opam config env`

    cd $git_repo/
    git clean -dfx
    cd $git_repo/sources
    
    ## A ## Test with 'opam pin'

    echo "=+= [travis.sh] $ocaml_version' compiler: test with 'opam pin'"

    opam pin add alt-ergo . --y ; exit_if_error

    non_regression

    opam remove alt-ergo

    ###########################################################################
    ## B ## Test with Makefile

    echo "=+= [travis.sh] $ocaml_version' compiler: test with Makefile"

    opam sw DUMMY
    eval `opam config env`
    opam sw remove $ocaml_version ; exit_if_error # should be fail !
    opam sw $ocaml_version ; exit_if_error
    eval `opam config env`

    opam install ocamlfind camlzip zarith ocplib-simplex lablgtk menhir --y ; exit_if_error

    cd $git_repo/
    git clean -dfx
    cd $git_repo/sources

    autoconf

    ./configure --prefix=$local_install_dir ; exit_if_error

    echo "=+= [travis.sh] building and installing ... =+="

    make -j4 alt-ergo ; exit_if_error
    make install-ae ; exit_if_error
    make clean ; exit_if_error

    make -j4 gui ; exit_if_error
    make install-gui ; exit_if_error
    make clean ; exit_if_error

    make -j4 fm-simplex ; exit_if_error
    make install-fm-simplex ; exit_if_error
    make clean ; exit_if_error

    echo "=+= [travis.sh] installed files in $local_install_dir ... =+="
    ls -R $local_install_dir
    export PATH=$PATH:$local_install_dir/bin

    non_regression

done
