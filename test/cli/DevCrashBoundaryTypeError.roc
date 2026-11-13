# The expect does not type check, so the dev backend runs it to a crash. The
# crash leaves through the crash boundary, which must still hold the frame it
# was set in. A release roc that tail-called into the test root lost that
# frame and segfaulted.

x : Str
x = "a"

expect x == 1
