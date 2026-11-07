import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 148 of the cap-16 certificate: slots 151552 .. 152575 -/
theorem chk_148 : chunkCheck 16 T stdSt 151552 1024 = true := by decide +kernel

end Row16
