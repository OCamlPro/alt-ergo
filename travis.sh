exit_if_error(){
    if [ "$?" -ne "0" ] ; then
        echo "exit if error triggered !"
        exit 1
    fi
}

local_install_dir=`pwd`/___local

git_repo=`pwd`

for ocaml_version in 4.06.0 4.05.0 4.04.0
do
    cd $git_repo/
    git clean -dfx
    echo "=+= [travis.sh] testing with OCaml version $ocaml_version =+="
    opam sw $ocaml_version ; exit_if_error
    eval `opam config env`
    opam update
    opam install ocamlfind camlzip zarith ocplib-simplex lablgtk menhir ; exit_if_error

    cd $git_repo/sources

    autoconf

    ./configure --prefix=$local_install_dir ; exit_if_error

    echo "=+= [travis.sh] building and installing ... =+="

    make -j4 alt-ergo ; exit_if_error
    make install ; exit_if_error
    make clean ; exit_if_error

    make -j4 gui ; exit_if_error
    make install-gui ; exit_if_error
    make clean ; exit_if_error

    make -j4 satML fm-simplex ; exit_if_error
    make install-satML install-fm-simplex ; exit_if_error
    make clean ; exit_if_error

    echo "before `pwd`"

    cd ../non-regression

    echo "after `pwd`"

    echo "=+= [travis.sh] installed files in $local_install_dir ... =+="
    ls -R $local_install_dir

    export PATH=$PATH:$local_install_dir/bin
    echo "which alt-ergo == `which alt-ergo`"
    echo "alt-ergo -version == `alt-ergo -version`"

    sh ./run_valid.sh "alt-ergo" "0.5" ; exit_if_error

    sh ./run_invalid.sh "alt-ergo" "0.5" ; exit_if_error

    # - make non-regression
done
