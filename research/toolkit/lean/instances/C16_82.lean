import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 82 of the cap-16 certificate: slots 83968 .. 84991 -/
theorem chk_82 : chunkCheck 16 T stdSt 83968 1024 = true := by decide +kernel

end Row16
