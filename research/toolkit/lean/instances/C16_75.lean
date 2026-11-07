import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 75 of the cap-16 certificate: slots 76800 .. 77823 -/
theorem chk_75 : chunkCheck 16 T stdSt 76800 1024 = true := by decide +kernel

end Row16
