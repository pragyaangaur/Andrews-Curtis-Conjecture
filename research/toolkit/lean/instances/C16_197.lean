import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 197 of the cap-16 certificate: slots 201728 .. 202751 -/
theorem chk_197 : chunkCheck 16 T stdSt 201728 1024 = true := by decide +kernel

end Row16
