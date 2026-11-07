import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 118 of the cap-16 certificate: slots 120832 .. 121855 -/
theorem chk_118 : chunkCheck 16 T stdSt 120832 1024 = true := by decide +kernel

end Row16
