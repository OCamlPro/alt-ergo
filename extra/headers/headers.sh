origin=`pwd`
conf=$origin/headache_config.txt
apache_ocp_nc=$origin/alt-ergo_header_apache.txt
ocp_nc=$origin/alt-ergo_header_ocamlpro.txt

cd ../../alt-ergo

for f in `find . -type f -name '*'` ; do
    if [ "`grep -c $f $origin/apache_files.txt`" = "0" ] ; then
        if [ "`grep -c $f $origin/ocamlpro_files.txt`" = "0" ] ; then
            if [ "`grep -c $f $origin/other_files.txt`" = "0" ] ; then
                # case 1: fail
                echo "extra/headers.sh: don't know which license to choose for file $f"
                exit 1
            else
                # case 2: do not change the file
                echo "file  $f: remains unchanged" > /dev/null
            fi
        else
            # case 3: Non-Commercial OCamlPro license
            echo "file  $f: put $ocp_nc" > /dev/null
            headache -c $conf -h $ocp_nc $f
        fi
    else
        # case 4: Apache + Non-Commercial OCamlPro license
        echo "file  $f: put $apache_ocp_nc" > /dev/null
        headache -c $conf -h $apache_ocp_nc $f
    fi
done

#
#headache -c $conf -h $apache_ocp_nc \
#		Makefile.configurable.in Makefile.users Makefile.developers Makefile \
#		configure.in README.md INSTALL.md \
#		src/*/*.ml src/*/*.ml[ily]
