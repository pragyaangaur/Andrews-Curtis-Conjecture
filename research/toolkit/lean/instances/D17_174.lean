import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 174 of the cap-17 certificate: slots 89088 .. 89599 -/
theorem chk_174 : chunkCheck 17 T stdSt 89088 512 = true := by decide +kernel

end Row17
