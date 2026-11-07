import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 194 of the cap-16 certificate: slots 198656 .. 199679 -/
theorem chk_194 : chunkCheck 16 T stdSt 198656 1024 = true := by decide +kernel

end Row16
