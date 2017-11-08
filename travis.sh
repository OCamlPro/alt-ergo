local_install_dir=`pwd`/___local

for ocaml_version in 4.06.0 4.05.0 4.04.0
do
    git clean -dfx
    echo "=+= [travis.sh] testing with OCaml version $ocaml_version =+="
    opam sw $ocaml_version
    eval `opam config env`
    opam update
    opam install ocamlfind camlzip zarith ocplib-simplex lablgtk menhir
    cd sources
    autoconf
    ./configure --prefix=$local_install_dir

    echo "=+= [travis.sh] building and installing ... =+="

    make -j4 alt-ergo
    make install
    make clean

    make -j4 gui
    make install-gui
    make clean

    make -j4 satML fm-simplex
    make install-satML install-fm-simplex
    make clean

    echo "before `pwd`"

    cd ../non-regression

    echo "after `pwd`"

    echo "=+= [travis.sh] installed files in $local_install_dir ... =+="
    ls -R $local_install_dir

    export PATH=$PATH:$local_install_dir/bin
    echo "which alt-ergo == `which alt-ergo`"
    echo "alt-ergo -version == `alt-ergo -version`"

    sh ./run_valid.sh "alt-ergo" "0.5"
    echo RETURN_CODE is $?

    sh ./run_invalid.sh "alt-ergo" "0.5"
    echo RETURN_CODE is $?

    cd ..
    # - make non-regression
done
