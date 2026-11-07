import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 254 of the cap-16 certificate: slots 260096 .. 261119 -/
theorem chk_254 : chunkCheck 16 T stdSt 260096 1024 = true := by decide +kernel

end Row16
