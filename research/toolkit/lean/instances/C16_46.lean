import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 46 of the cap-16 certificate: slots 47104 .. 48127 -/
theorem chk_46 : chunkCheck 16 T stdSt 47104 1024 = true := by decide +kernel

end Row16
