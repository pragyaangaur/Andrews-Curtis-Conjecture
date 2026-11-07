import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 115 of the cap-16 certificate: slots 117760 .. 118783 -/
theorem chk_115 : chunkCheck 16 T stdSt 117760 1024 = true := by decide +kernel

end Row16
