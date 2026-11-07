import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 200 of the cap-16 certificate: slots 204800 .. 205823 -/
theorem chk_200 : chunkCheck 16 T stdSt 204800 1024 = true := by decide +kernel

end Row16
