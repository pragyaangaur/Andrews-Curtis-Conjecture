import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 436 of the cap-17 certificate: slots 223232 .. 223743 -/
theorem chk_436 : chunkCheck 17 T stdSt 223232 512 = true := by decide +kernel

end Row17
