import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 156 of the cap-16 certificate: slots 159744 .. 160767 -/
theorem chk_156 : chunkCheck 16 T stdSt 159744 1024 = true := by decide +kernel

end Row16
