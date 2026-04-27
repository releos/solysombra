#!/usr/bin/env python3
"""
ShadowMap España — Preprocesador nacional v1
=============================================
Descarga y procesa los datos de edificios de toda España desde el
Catastro INSPIRE (Dirección General del Catastro).

Fuente de datos:
  Atom feed: https://www.catastro.meh.es/INSPIRE/buildings/ES.SDGC.BU.atom.xml
  Licencia:  Reutilización de la información del Sector Público (RISP).
             Requiere citar "© Dirección General del Catastro".

Formato de salida (idéntico al preprocesador de Madrid):
  data/tiles/{lon}_{lat}.json  → [{maxH, hull, polys:[{h, ring}]}]
  data/meta.json               → metadatos globales
  data/processed.json          → municipios procesados (para reanudar)

Alturas:
  1. heightAboveGround en el GML          → valor directo (metros)
  2. numberOfFloorsAboveGround × 3.1 m   → estimación por plantas
  3. Sin datos                            → 4.0 m (planta baja por defecto)

Coordenadas:
  El Catastro sirve en EPSG:25830 (UTM huso 30N / ETRS89).
  Se convierten a WGS84 lon/lat con la fórmula de Helmert inversa
  (error < 0.5m para toda España peninsular, válido para sombras).

Uso:
    pip install requests
    python preprocess_spain.py                    # toda España
    python preprocess_spain.py --province 28      # solo una provincia (código INE)
    python preprocess_spain.py --resume           # salta municipios ya procesados
    python preprocess_spain.py --workers 12       # más hilos de descarga
    python preprocess_spain.py --list-provinces   # listar provincias disponibles

Nota sobre tamaño:
  ~8.125 municipios × ~50 KB/zip ≈ ~400 MB de descarga en crudo.
  Resultado: ~180.000 tiles × ~8 KB/tile ≈ ~1.5 GB de datos procesados.
  Tiempo estimado con 8 workers: 3-6 horas según conexión.
"""

import argparse
import io
import json
import math
import os
import re
import sys
import time
import traceback
import xml.etree.ElementTree as ET
import zipfile
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from threading import Lock

import requests

# ── Configuración ─────────────────────────────────────────────────────────────
ATOM_ROOT   = "https://www.catastro.meh.es/INSPIRE/buildings/ES.SDGC.BU.atom.xml"
TILE_DEG    = 0.004          # mismo que el preprocesador de Madrid
ADJ_BUF     = 0.000001       # ~0.1m: solo une partes del mismo edificio
M_PER_FLOOR = 3.1            # altura media por planta en España
MIN_HEIGHT  = 3.0            # altura mínima (planta baja)
DEFAULT_H   = 4.0            # si no hay datos de altura ni plantas
MAX_WORKERS = 8              # hilos paralelos de descarga/proceso
RETRY_MAX   = 3              # reintentos por municipio fallido
TIMEOUT     = 60             # segundos por petición HTTP

OUT_DIR       = Path("data/tiles")
META_PATH     = Path("data/meta.json")
PROCESSED_LOG = Path("data/processed.json")
ERROR_LOG     = Path("data/errors.json")

# Namespaces GML / INSPIRE
NS = {
    "atom":    "http://www.w3.org/2005/Atom",
    "gml":     "http://www.opengis.net/gml/3.2",
    "bu-base": "http://inspire.ec.europa.eu/schemas/bu-base/4.0",
    "bu-ext2d":"http://inspire.ec.europa.eu/schemas/bu-ext2d/4.0",
    "xlink":   "http://www.w3.org/1999/xlink",
}

# ── UTM ETRS89 huso 30N → WGS84 ──────────────────────────────────────────────
# Fórmula de Helmert inversa para el elipsoide GRS80.
# Válida para España peninsular y Baleares (husos 29-31, pero el Catastro usa 30).
# Error < 0.5m respecto a pyproj — suficiente para sombras urbanas.

_A  = 6378137.0          # semieje mayor GRS80
_F  = 1/298.257222101    # achatamiento
_B  = _A*(1-_F)
_E2 = 1-((_B/_A)**2)
_K0 = 0.9996
_E0 = 500000.0           # falso este
_N0 = 0.0                # falso norte (hemisferio norte)
_L0 = math.radians(-3.0) # meridiano central huso 30N

def _utm30_to_wgs84(easting, northing):
    """Convierte UTM huso 30N (ETRS89≈WGS84) a (lon, lat) en grados."""
    x = easting - _E0
    y = northing - _N0
    e2  = _E2
    e12 = e2/(1-e2)
    M   = y/_K0
    mu  = M/(_A*(1 - e2/4 - 3*e2**2/64 - 5*e2**3/256))
    e1  = (1-math.sqrt(1-e2))/(1+math.sqrt(1-e2))
    p1  = mu + (3*e1/2 - 27*e1**3/32)*math.sin(2*mu)
    p1 += (21*e1**2/16 - 55*e1**4/32)*math.sin(4*mu)
    p1 += (151*e1**3/96)*math.sin(6*mu)
    p1 += (1097*e1**4/512)*math.sin(8*mu)
    N1  = _A/math.sqrt(1-e2*math.sin(p1)**2)
    T1  = math.tan(p1)**2
    C1  = e12*math.cos(p1)**2
    R1  = _A*(1-e2)/(1-e2*math.sin(p1)**2)**1.5
    D   = x/(_K0*N1)
    lat = p1 - (N1*math.tan(p1)/R1)*(
        D**2/2 - (5+3*T1+10*C1-4*C1**2-9*e12)*D**4/24 +
        (61+90*T1+298*C1+45*T1**2-252*e12-3*C1**2)*D**6/720
    )
    lon = _L0 + (
        D - (1+2*T1+C1)*D**3/6 +
        (5-2*C1+28*T1-3*C1**2+8*e12+24*T1**2)*D**5/120
    )/math.cos(p1)
    return round(math.degrees(lon), 7), round(math.degrees(lat), 7)


def _is_geographic(srs_name):
    """True si las coordenadas ya están en grados (lon/lat)."""
    return "4326" in srs_name or "CRS84" in srs_name or "EPSG::4258" in srs_name


# ── Geometría (idéntica al preprocesador de Madrid) ──────────────────────────
def cross(O, A, B):
    return (A[0]-O[0])*(B[1]-O[1]) - (A[1]-O[1])*(B[0]-O[0])

def convex_hull(pts):
    pts = sorted(set(map(tuple, pts)))
    if len(pts) < 3: return list(pts)
    lo, hi = [], []
    for p in pts:
        while len(lo) >= 2 and cross(lo[-2], lo[-1], p) <= 0: lo.pop()
        lo.append(p)
    for p in reversed(pts):
        while len(hi) >= 2 and cross(hi[-2], hi[-1], p) <= 0: hi.pop()
        hi.append(p)
    return lo[:-1] + hi[:-1]

def bbox_of(pts):
    xs = [p[0] for p in pts]; ys = [p[1] for p in pts]
    return min(xs), min(ys), max(xs), max(ys)

def bboxes_intersect(a, b, buf=0.0):
    return (a[0]-buf <= b[2] and a[2]+buf >= b[0] and
            a[1]-buf <= b[3] and a[3]+buf >= b[1])

class UF:
    def __init__(self, n):
        self.p = list(range(n)); self.r = [0]*n
    def find(self, i):
        while self.p[i] != i: self.p[i] = self.p[self.p[i]]; i = self.p[i]
        return i
    def union(self, i, j):
        ri, rj = self.find(i), self.find(j)
        if ri == rj: return
        if   self.r[ri] < self.r[rj]: self.p[ri] = rj
        elif self.r[ri] > self.r[rj]: self.p[rj] = ri
        else: self.p[rj] = ri; self.r[ri] += 1

def snap_tile(v): return math.floor(v / TILE_DEG) * TILE_DEG
def tile_key(tx, ty): return f"{round(tx,4):.4f}_{round(ty,4):.4f}"


# ── Parser GML del Catastro ───────────────────────────────────────────────────
def _parse_pos_list(text, geographic):
    """
    Convierte una gml:posList a lista de (lon, lat).
    El GML del Catastro puede ser 'lat lon' o 'easting northing' según el SRS.
    """
    nums = list(map(float, text.split()))
    pts  = []
    for i in range(0, len(nums)-1, 2):
        a, b = nums[i], nums[i+1]
        if geographic:
            # posList en grados: el Catastro usa 'lat lon' (eje1=lat, eje2=lon)
            lon, lat = round(b, 7), round(a, 7)
        else:
            # UTM: 'easting northing'
            lon, lat = _utm30_to_wgs84(a, b)
        if -20.0 <= lon <= 5.0 and 27.0 <= lat <= 44.5:  # bbox España + Canarias
            pts.append((lon, lat))
    return pts


def _extract_polygons_from_element(elem, geographic):
    """
    Recorre un elemento GML buscando gml:Polygon / gml:Surface y devuelve
    lista de rings (listas de puntos) para el anillo exterior.
    """
    rings = []
    # gml:Polygon → gml:exterior → gml:LinearRing → gml:posList
    for poly in elem.iter(f"{{{NS['gml']}}}Polygon"):
        for ext in poly.findall(f"{{{NS['gml']}}}exterior"):
            for lr in ext.findall(f"{{{NS['gml']}}}LinearRing"):
                pl = lr.find(f"{{{NS['gml']}}}posList")
                if pl is not None and pl.text:
                    pts = _parse_pos_list(pl.text.strip(), geographic)
                    if len(pts) >= 3:
                        rings.append(pts)
    # gml:Surface / gml:PolyhedralSurface → mismo patrón
    for surf in elem.iter(f"{{{NS['gml']}}}Surface"):
        for patch in surf.iter(f"{{{NS['gml']}}}PolygonPatch"):
            for ext in patch.findall(f"{{{NS['gml']}}}exterior"):
                for lr in ext.findall(f"{{{NS['gml']}}}LinearRing"):
                    pl = lr.find(f"{{{NS['gml']}}}posList")
                    if pl is not None and pl.text:
                        pts = _parse_pos_list(pl.text.strip(), geographic)
                        if len(pts) >= 3:
                            rings.append(pts)
    return rings


def parse_gml_buildings(gml_bytes):
    """
    Parsea un fichero GML del Catastro INSPIRE y devuelve una lista de features
    en el mismo formato que usa group_buildings():
      [{"properties": {"h": float}, "geometry": {"type": "Polygon",
        "coordinates": [[(lon, lat), ...]]}}]
    """
    try:
        root = ET.fromstring(gml_bytes)
    except ET.ParseError as e:
        print(f"    ⚠ ParseError GML: {e}")
        return []

    # Detectar SRS del featureCollection o del primer feature
    srs_name = (root.get("srsName") or
                root.get(f"{{{NS['gml']}}}srsName") or "EPSG::25830")
    geographic = _is_geographic(srs_name)

    features = []

    # Iterar sobre BuildingPart (INSPIRE) y Building
    tags = [
        f"{{{NS['bu-ext2d']}}}BuildingPart",
        f"{{{NS['bu-ext2d']}}}Building",
        f"{{{NS['bu-base']}}}BuildingPart",
        f"{{{NS['bu-base']}}}Building",
    ]
    for tag in tags:
        for elem in root.iter(tag):
            # ── Altura ──────────────────────────────────────────────────
            h = None

            # 1. Altura real en metros (heightAboveGround)
            for hag_tag in [
                f"{{{NS['bu-base']}}}heightAboveGround",
                "heightAboveGround",
            ]:
                hag = elem.find(f".//{hag_tag}")
                if hag is not None:
                    # puede ser <heightAboveGround uom="m">12.5</heightAboveGround>
                    # o <heightAboveGround><value>12.5</value></heightAboveGround>
                    try:
                        val = float((hag.text or "").strip()) if hag.text else None
                        if val is None:
                            v_elem = hag.find("value") or hag.find("Value")
                            if v_elem is not None:
                                val = float(v_elem.text.strip())
                        if val and val > 0:
                            h = val
                            break
                    except (ValueError, AttributeError):
                        pass

            # 2. Plantas × M_PER_FLOOR
            if h is None:
                for floors_tag in [
                    f"{{{NS['bu-ext2d']}}}numberOfFloorsAboveGround",
                    f"{{{NS['bu-base']}}}numberOfFloorsAboveGround",
                    "numberOfFloorsAboveGround",
                ]:
                    fe = elem.find(f".//{floors_tag}")
                    if fe is not None and fe.text:
                        try:
                            floors = int(fe.text.strip())
                            if floors > 0:
                                h = floors * M_PER_FLOOR
                                break
                        except ValueError:
                            pass

            if h is None:
                h = DEFAULT_H
            h = max(MIN_HEIGHT, h)

            # ── Geometría ───────────────────────────────────────────────
            # Buscar en bu-base:geometry2D → bu-base:BuildingGeometry2D → bu-base:geometry
            geom_elem = elem
            for geom2d in elem.iter(f"{{{NS['bu-base']}}}geometry2D"):
                geom_elem = geom2d
                break

            # También puede estar directamente como gml:Polygon hijo
            rings = _extract_polygons_from_element(geom_elem, geographic)
            if not rings and geom_elem is not elem:
                rings = _extract_polygons_from_element(elem, geographic)

            for ring in rings:
                features.append({
                    "properties": {"h": round(h, 1)},
                    "geometry": {"type": "Polygon",
                                 "coordinates": [[(p[0], p[1]) for p in ring]]}
                })

    return features


# ── Agrupación (idéntica al preprocesador de Madrid) ─────────────────────────
def group_buildings(features):
    n = len(features)
    if n == 0:
        return []

    feat_rings   = []
    feat_bboxes  = []

    for f in features:
        h    = f["properties"]["h"]
        geom = f["geometry"]
        pts  = [(round(v[0], 7), round(v[1], 7))
                for v in geom["coordinates"][0]]
        feat_rings.append({"h": h, "ring": pts})
        feat_bboxes.append(bbox_of(pts) if pts else (0, 0, 0, 0))

    order = sorted(range(n), key=lambda i: feat_bboxes[i][0])
    uf    = UF(n)
    for oi, i in enumerate(order):
        bi = feat_bboxes[i]
        for oj in range(oi + 1, len(order)):
            j  = order[oj]
            bj = feat_bboxes[j]
            if bj[0] > bi[2] + ADJ_BUF: break
            if bboxes_intersect(bi, bj, ADJ_BUF): uf.union(i, j)

    groups_map = defaultdict(list)
    for i in range(n):
        groups_map[uf.find(i)].append(i)

    buildings = []
    for indices in groups_map.values():
        all_pts, polys, max_h = [], [], 0.0
        for idx in indices:
            rd = feat_rings[idx]
            h, ring = rd["h"], rd["ring"]
            if not ring: continue
            polys.append({"h": round(h, 1),
                          "ring": [[round(x, 6), round(y, 6)] for x, y in ring]})
            all_pts.extend(ring)
            if h > max_h: max_h = h
        if not polys: continue
        hull = convex_hull(all_pts)
        if len(hull) < 3: continue
        buildings.append({
            "maxH": round(max_h, 1),
            "hull": [[round(x, 6), round(y, 6)] for x, y in hull],
            "polys": polys,
        })

    return buildings


# ── Tiles ─────────────────────────────────────────────────────────────────────
_tile_lock = Lock()
_tile_cache: dict[str, list] = {}   # clave → lista de buildings

def flush_tiles_to_disk(force=False):
    """Escribe el caché de tiles al disco. Si force=False, solo escribe los grandes."""
    global _tile_cache
    with _tile_lock:
        keys = list(_tile_cache.keys())
    for key in keys:
        with _tile_lock:
            blds = _tile_cache.get(key, [])
        path = OUT_DIR / f"{key}.json"
        # Leer tile existente si hay
        existing = []
        if path.exists():
            try:
                existing = json.loads(path.read_text())
            except Exception:
                existing = []
        merged = existing + blds
        path.write_text(json.dumps(merged, separators=(",", ":")))
        with _tile_lock:
            _tile_cache.pop(key, None)


def add_buildings_to_tiles(buildings):
    """Acumula buildings en el caché de tiles (thread-safe)."""
    with _tile_lock:
        for bld in buildings:
            hull = bld["hull"]
            cx = sum(p[0] for p in hull) / len(hull)
            cy = sum(p[1] for p in hull) / len(hull)
            key = tile_key(snap_tile(cx), snap_tile(cy))
            _tile_cache.setdefault(key, []).append(bld)
        # Flush si el caché crece demasiado
        if sum(len(v) for v in _tile_cache.values()) > 50_000:
            flush_tiles_to_disk()


# ── Atom feed ─────────────────────────────────────────────────────────────────
def _get(url, retries=3, timeout=TIMEOUT):
    for attempt in range(retries):
        try:
            r = requests.get(url, timeout=timeout,
                             headers={"User-Agent": "ShadowMap/1.0 (+https://github.com/shadowmap-madrid)"})
            r.raise_for_status()
            return r
        except Exception as e:
            if attempt == retries - 1: raise
            time.sleep(2 ** attempt)


def fetch_atom_provinces():
    """Devuelve lista de (province_name, feed_url) desde el Atom raíz."""
    r   = _get(ATOM_ROOT)
    root = ET.fromstring(r.content)
    entries = []
    for entry in root.findall(f"{{{NS['atom']}}}entry"):
        title = entry.findtext(f"{{{NS['atom']}}}title") or ""
        for link in entry.findall(f"{{{NS['atom']}}}link"):
            if link.get("type") == "application/atom+xml":
                entries.append((title.strip(), link.get("href")))
                break
    return entries


def fetch_atom_municipalities(prov_feed_url):
    """
    Devuelve lista de (muni_code, muni_name, zip_url) para una provincia.
    zip_url apunta al zip con los ficheros GML.
    """
    r    = _get(prov_feed_url)
    root = ET.fromstring(r.content)
    munis = []
    for entry in root.findall(f"{{{NS['atom']}}}entry"):
        title = entry.findtext(f"{{{NS['atom']}}}title") or ""
        # El ID del municipio está en el <id> o en el <title>
        muni_id = entry.findtext(f"{{{NS['atom']}}}id") or ""
        # Buscar link al zip de buildings
        zip_url = None
        for link in entry.findall(f"{{{NS['atom']}}}link"):
            href = link.get("href", "")
            # Queremos el zip de BUILDING (footprints), no BUILDINGPART_ADDRESS
            if href.endswith(".zip") and "BUILDING" in href.upper():
                zip_url = href
                break
        if not zip_url:
            # Fallback: cualquier zip
            for link in entry.findall(f"{{{NS['atom']}}}link"):
                href = link.get("href", "")
                if href.endswith(".zip"):
                    zip_url = href
                    break
        if zip_url:
            # Extraer código de municipio del título o URL
            match = re.search(r'(\d{5})', title) or re.search(r'(\d{5})', zip_url)
            muni_code = match.group(1) if match else title.strip()[:10]
            munis.append((muni_code, title.strip(), zip_url))
    return munis


# ── Proceso por municipio ──────────────────────────────────────────────────────
def process_municipality(muni_code, muni_name, zip_url):
    """
    Descarga el zip de un municipio, extrae los GML, parsea los edificios,
    los agrupa y los añade a los tiles. Devuelve n_buildings procesados.
    """
    for attempt in range(RETRY_MAX):
        try:
            r      = _get(zip_url, retries=2, timeout=120)
            zf     = zipfile.ZipFile(io.BytesIO(r.content))
            all_features = []

            for name in zf.namelist():
                # Buscar ficheros GML con geometría de edificios
                # Nombres típicos: {CODE}_BUILDING.gml, building.gml, edificios.gml
                nl = name.lower()
                if nl.endswith(".gml") and ("building" in nl or "edificio" in nl):
                    gml_bytes = zf.read(name)
                    feats = parse_gml_buildings(gml_bytes)
                    all_features.extend(feats)

            if not all_features:
                # Intentar con cualquier GML si no encontramos el esperado
                for name in zf.namelist():
                    if name.lower().endswith(".gml"):
                        gml_bytes = zf.read(name)
                        feats = parse_gml_buildings(gml_bytes)
                        all_features.extend(feats)
                        if all_features:
                            break

            buildings = group_buildings(all_features)
            if buildings:
                add_buildings_to_tiles(buildings)
            return len(buildings)

        except Exception as e:
            if attempt == RETRY_MAX - 1:
                raise RuntimeError(f"{muni_code} ({muni_name}): {e}") from e
            time.sleep(3 * (attempt + 1))


# ── Metadatos ─────────────────────────────────────────────────────────────────
def load_processed():
    if PROCESSED_LOG.exists():
        try:
            return set(json.loads(PROCESSED_LOG.read_text()))
        except Exception:
            pass
    return set()

def save_processed(processed_set):
    PROCESSED_LOG.write_text(json.dumps(sorted(processed_set), indent=2))

def load_errors():
    if ERROR_LOG.exists():
        try:
            return json.loads(ERROR_LOG.read_text())
        except Exception:
            pass
    return {}

def save_errors(errors):
    ERROR_LOG.write_text(json.dumps(errors, indent=2, ensure_ascii=False))

def export_meta():
    """Genera meta.json con estadísticas globales de los tiles."""
    if not OUT_DIR.exists():
        return
    tiles    = list(OUT_DIR.glob("*.json"))
    n_tiles  = len(tiles)
    n_blds   = 0
    min_lon, min_lat, max_lon, max_lat = 9999, 9999, -9999, -9999
    for tf in tiles:
        try:
            data = json.loads(tf.read_text())
            n_blds += len(data)
            for bld in data:
                for p in bld.get("hull", []):
                    min_lon = min(min_lon, p[0]); max_lon = max(max_lon, p[0])
                    min_lat = min(min_lat, p[1]); max_lat = max(max_lat, p[1])
        except Exception:
            pass
    META_PATH.parent.mkdir(parents=True, exist_ok=True)
    META_PATH.write_text(json.dumps({
        "generated":  time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "source":     "Dirección General del Catastro — INSPIRE BU v4.0",
        "license":    "Reutilización de la información del Sector Público (RISP). © DGC",
        "buildings":  n_blds,
        "tiles":      n_tiles,
        "tile_deg":   TILE_DEG,
        "adj_buf":    ADJ_BUF,
        "m_per_floor": M_PER_FLOOR,
        "bbox": {
            "w": round(min_lon, 5), "s": round(min_lat, 5),
            "e": round(max_lon, 5), "n": round(max_lat, 5),
        },
    }, indent=2))
    print(f"✓ meta.json — {n_blds:,} edificios en {n_tiles:,} tiles")


# ── Punto de entrada ──────────────────────────────────────────────────────────
def main():
    parser = argparse.ArgumentParser(
        description="ShadowMap España — Preprocesador nacional Catastro INSPIRE"
    )
    parser.add_argument("--province",       type=str, default=None,
                        help="Código INE de provincia (2 dígitos). Ej: 28 (Madrid)")
    parser.add_argument("--resume",         action="store_true",
                        help="Saltar municipios ya procesados")
    parser.add_argument("--workers",        type=int, default=MAX_WORKERS,
                        help=f"Hilos paralelos (default: {MAX_WORKERS})")
    parser.add_argument("--list-provinces", action="store_true",
                        help="Listar provincias disponibles y salir")
    parser.add_argument("--meta-only",      action="store_true",
                        help="Solo regenerar meta.json a partir de tiles existentes")
    args = parser.parse_args()

    print("═" * 56)
    print("ShadowMap España — Preprocesador nacional v1")
    print("Fuente: Catastro INSPIRE — © DGC (licencia RISP)")
    print("═" * 56)

    if args.meta_only:
        export_meta(); return

    # ── Obtener lista de provincias ────────────────────────────────────────
    print("Obteniendo índice de provincias del Atom feed...")
    provinces = fetch_atom_provinces()
    print(f"  {len(provinces)} provincias encontradas")

    if args.list_provinces:
        print("\nProvincias disponibles:")
        for i, (name, url) in enumerate(provinces, 1):
            code = re.search(r'/(\d+)/', url)
            c = code.group(1) if code else str(i).zfill(2)
            print(f"  {c:>4}  {name}")
        return

    # Filtrar por provincia si se especificó
    if args.province:
        provinces = [(n, u) for n, u in provinces if args.province in u or args.province in n]
        if not provinces:
            print(f"✗ No se encontró la provincia '{args.province}'")
            sys.exit(1)
        print(f"  Filtrando: {len(provinces)} provincia(s) con código '{args.province}'")

    # ── Recopilar todos los municipios ─────────────────────────────────────
    print("\nObteniendo lista de municipios...")
    all_munis = []
    for prov_name, prov_url in provinces:
        try:
            munis = fetch_atom_municipalities(prov_url)
            all_munis.extend(munis)
            print(f"  {prov_name}: {len(munis)} municipios", end="\r")
        except Exception as e:
            print(f"\n  ⚠ Error en provincia {prov_name}: {e}")
    print(f"\n✓ {len(all_munis):,} municipios en total")

    # Resume: filtrar los ya procesados
    processed = load_processed() if args.resume else set()
    errors    = load_errors()
    pending   = [(c, n, u) for c, n, u in all_munis if c not in processed]
    print(f"  {len(processed):,} ya procesados, {len(pending):,} pendientes")

    if not pending:
        print("✓ Todo ya procesado. Usa --meta-only para regenerar meta.json")
        export_meta(); return

    # ── Procesar en paralelo ───────────────────────────────────────────────
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    t0         = time.time()
    done       = 0
    total_blds = 0
    lock_log   = Lock()

    print(f"\nProcesando con {args.workers} workers...\n")

    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = {
            pool.submit(process_municipality, c, n, u): (c, n)
            for c, n, u in pending
        }
        for fut in as_completed(futures):
            muni_code, muni_name = futures[fut]
            try:
                n_blds = fut.result()
                total_blds += n_blds
                with lock_log:
                    processed.add(muni_code)
                    errors.pop(muni_code, None)
                    done += 1
                    elapsed  = time.time() - t0
                    rate     = done / elapsed if elapsed > 0 else 0
                    remaining = (len(pending) - done) / rate if rate > 0 else 0
                    print(
                        f"  [{done:>5}/{len(pending)}] {muni_code} {muni_name[:30]:<30}"
                        f"  +{n_blds:>5} edificios"
                        f"  ETA {remaining/60:.0f} min",
                        end="\r"
                    )
            except Exception as e:
                with lock_log:
                    errors[muni_code] = str(e)
                    done += 1
                    print(f"\n  ⚠ Error {muni_code} ({muni_name[:25]}): {e}")

            # Guardar progreso cada 50 municipios
            if done % 50 == 0:
                with lock_log:
                    save_processed(processed)
                    save_errors(errors)
                flush_tiles_to_disk()

    # Flush final
    flush_tiles_to_disk(force=True)
    save_processed(processed)
    save_errors(errors)

    elapsed = time.time() - t0
    print(f"\n\n✓ {done:,} municipios procesados en {elapsed/60:.1f} min")
    print(f"✓ {total_blds:,} edificios agrupados")
    if errors:
        print(f"⚠ {len(errors)} errores guardados en {ERROR_LOG}")
        print("  Vuelve a ejecutar con --resume para reintentarlos")

    export_meta()
    print("═" * 56)
    print("✓ Listo. Sube data/ al repositorio GitHub.")
    print("═" * 56)


if __name__ == "__main__":
    main()
