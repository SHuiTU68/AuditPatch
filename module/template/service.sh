resetprop -w sys.boot_completed 0
setprop ctl.restart logd
MODDIR=${0%/*}
INJECTOR_PATH="${MODDIR}/bin/Injector"
LIB_PATH="/system/lib64/libauditpatch.so"
TARGET_PROC="/system/bin/logd"
chmod +x $INJECTOR_PATH
$INJECTOR_PATH -p $TARGET_PROC -l $LIB_PATH
# Android 17 native isolated-process incubator. The scanner's app_zygote
# carrier is a short-lived USAP child, so the only way to reach it is to hook
# the parent it is forked from; the library is then inherited by every child.
TARGET_ZYGOTE="/system/bin/zygote_next"
$INJECTOR_PATH -p $TARGET_ZYGOTE -l $LIB_PATH