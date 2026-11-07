import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 106 of the cap-16 certificate: slots 108544 .. 109567 -/
theorem chk_106 : chunkCheck 16 T stdSt 108544 1024 = true := by decide +kernel

end Row16
