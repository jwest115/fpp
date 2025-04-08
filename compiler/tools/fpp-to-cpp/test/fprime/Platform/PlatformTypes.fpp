#####
# PlatformTypes.fpp:
#
# Define platform type alias within this file. To maintain C-compatibility
# leave definitions in global scope.
####

@ The unsigned type of larger sizes internal to the software,
@ e.g., memory buffer sizes, file sizes. Must be unsigned.
@ Supplied by platform, overridable by project.
type PlatformSizeType = U64

@ The signed type of larger sizes internal to the software, used
@ for signed offsets, e.g., file seek offsets. Must be signed.
type PlatformSignedSizeType = I64

@ The type of smaller indicies internal to the software, used
@ for array indicies, e.g., port indicies. Must be signed.
type PlatformIndexType = I16

@ The type of arguments to assert functions. Supplied by platform,
@ overridable by project.
type PlatformAssertArgType = I32

@ The type of task priorities used. Supplied by platform,
@ overridable by project.
type PlatformTaskPriorityType = U8

@ The type of queue priorities used. Supplied by platform,
@ overridable by project.
type PlatformQueuePriorityType = U8
