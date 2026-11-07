import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 157 of the cap-16 certificate: slots 160768 .. 161791 -/
theorem chk_157 : chunkCheck 16 T stdSt 160768 1024 = true := by decide +kernel

end Row16
