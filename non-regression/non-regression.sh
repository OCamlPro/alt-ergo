#!/bin/bash

# Exit if one of the scripts fails
set -e

echo "===== [ with Tableaux ] ======================================================================================";
./main_script.sh "--sat-solver Tableaux"

echo "===== [ with CDCL-Tableaux ] =================================================================================";
./main_script.sh "--sat-solver CDCL-Tableaux"

echo "===== [ with CDCL ] ==========================================================================================";
./main_script.sh "--sat-solver CDCL"

echo "===== [ with Tableaux-CDCL ] =================================================================================";
./main_script.sh "--sat-solver Tableaux-CDCL"

echo "===== [ WITH FM-SIMPLEX ] ====================================================================================";
./main_script.sh "--inequalities-plugin `pwd`/../sources/_build/install/default/lib/plugins/fm-simplex-plugin.cmxs"
