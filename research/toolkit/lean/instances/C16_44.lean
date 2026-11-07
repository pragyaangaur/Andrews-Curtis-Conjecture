import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 44 of the cap-16 certificate: slots 45056 .. 46079 -/
theorem chk_44 : chunkCheck 16 T stdSt 45056 1024 = true := by decide +kernel

end Row16
