import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 23 of the cap-16 certificate: slots 23552 .. 24575 -/
theorem chk_23 : chunkCheck 16 T stdSt 23552 1024 = true := by decide +kernel

end Row16
