# Neon Desktop Pet

Neon is a cyberpunk desktop companion built with Python and Tkinter. It wanders between desktop icons, hops and crawls along screen edges, and can teleport to a random on-screen location.

## Run Neon

Use Windows with Python 3 and Tkinter. From this folder, run:

```powershell
python .\neon_pet.py
```

Keep the `assets` folder beside `neon_pet.py`; it contains the animation frames. Pillow is optional. Install it with `python -m pip install pillow` for rotated wall and ceiling poses and squash-and-stretch hop effects.

On 4K displays Neon scales up automatically. To set a specific scale for one launch:

```powershell
$env:NEON_SCALE = "2"
python .\neon_pet.py
```

## Controls and features

- Click Neon to pet it; drag it to reposition it.
- Use the fixed toolbar to feed, play, or open the menu. Right-click Neon for the full menu.
- Neon can patrol desktop icons, pause its patrol, crawl along the ceiling and screen edges, and run zoomies.
- Choose **Teleport randomly** in the menu for a charging circle, a random screen jump, and fading afterimages.
- Open **Neon settings** to adjust the glow color, movement pace, menu text size, speech voice, speech pace and volume, and auto-feed interval.
- Speech preview and one-time voice commands use Windows speech services.

## Feeding and temporary files

Manual **Junk Snack** shows a review list of eligible files older than seven days in selected temporary, cache, and Windows error-report folders. Nothing is selected by default; choose files explicitly before Neon removes them.

When auto-feed is enabled, Neon checks at the configured interval. If its hunger is below 55%, it may remove up to three regular files older than seven days from the user’s temporary folder, without opening the manual review list. Turn auto-feed off in the menu or Settings to stop these automatic checks.

## Saved settings and updates

Neon saves its state and preferences in `~/.neon_pet_state.json` in your Windows user folder, with a `.bak` backup.

The optional `neon.zip` package contains the app and assets. At startup, Neon checks for a package with a higher `APP_VERSION`, validates its Python syntax, and uses a health check with rollback if startup fails. Keep the ZIP beside `neon_pet.py` if you use this updater.
