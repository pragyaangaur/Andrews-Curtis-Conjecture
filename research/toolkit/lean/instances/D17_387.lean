import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 387 of the cap-17 certificate: slots 198144 .. 198655 -/
theorem chk_387 : chunkCheck 17 T stdSt 198144 512 = true := by decide +kernel

end Row17
