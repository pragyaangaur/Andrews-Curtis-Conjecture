import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 172 of the cap-17 certificate: slots 88064 .. 88575 -/
theorem chk_172 : chunkCheck 17 T stdSt 88064 512 = true := by decide +kernel

end Row17
