import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 51 of the cap-16 certificate: slots 52224 .. 53247 -/
theorem chk_51 : chunkCheck 16 T stdSt 52224 1024 = true := by decide +kernel

end Row16
