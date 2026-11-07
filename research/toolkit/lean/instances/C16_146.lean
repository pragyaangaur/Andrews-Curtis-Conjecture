import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 146 of the cap-16 certificate: slots 149504 .. 150527 -/
theorem chk_146 : chunkCheck 16 T stdSt 149504 1024 = true := by decide +kernel

end Row16
