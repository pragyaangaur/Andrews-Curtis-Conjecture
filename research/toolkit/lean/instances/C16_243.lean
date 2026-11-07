import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 243 of the cap-16 certificate: slots 248832 .. 249855 -/
theorem chk_243 : chunkCheck 16 T stdSt 248832 1024 = true := by decide +kernel

end Row16
