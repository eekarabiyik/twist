
// nohup /net/apps/magma-2.27-2/magma -t 32 "run_all.m" &


global_time:=Realtime();

load "FindUnentangledAgreeable.m";

load "FindAgreeable.m";

load "FindHighGenusModels.m";

load "FindCommutatorInfo.m";

load "FindAbelianCovers.m";

load "PointSearch.m";

Realtime(global_time);

exit;



