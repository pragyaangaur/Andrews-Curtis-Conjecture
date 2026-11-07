import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 169 of the cap-16 certificate: slots 173056 .. 174079 -/
theorem chk_169 : chunkCheck 16 T stdSt 173056 1024 = true := by decide +kernel

end Row16
