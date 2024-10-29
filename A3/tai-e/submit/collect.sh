TAIE_DIR=$(pwd)/src/main/java/pascal/taie &&
cp $TAIE_DIR/analysis/dataflow/analysis/DeadCodeDetection.java ./submit &&
cd submit &&
zip ./A3.zip ./*.java &&
cd ..