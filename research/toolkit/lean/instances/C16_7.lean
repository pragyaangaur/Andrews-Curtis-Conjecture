import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 7 of the cap-16 certificate: slots 7168 .. 8191 -/
theorem chk_7 : chunkCheck 16 T stdSt 7168 1024 = true := by decide +kernel

end Row16
