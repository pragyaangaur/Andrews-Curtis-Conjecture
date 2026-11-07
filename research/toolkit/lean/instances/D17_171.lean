import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 171 of the cap-17 certificate: slots 87552 .. 88063 -/
theorem chk_171 : chunkCheck 17 T stdSt 87552 512 = true := by decide +kernel

end Row17
