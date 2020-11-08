# -*- coding: utf-8 -*-
# Copyright 2020 ACSONE SA/NV
import logging
from psycopg2.extensions import AsIs
from odoo import tools

from odoo import SUPERUSER_ID, api

_logger = logging.getLogger(__name__)

def migrate(cr, version):
    default_lang = (tools.config.get('load_language') or 'en_US').split(',')[0]
    cols = ["name", "description", "description_purchase", "description_sale"]
    with api.Environment.manage():
        env = api.Environment(cr, SUPERUSER_ID, {})
        lang_codes = [i[0] for i in env["res.lang"].get_installed()]

        for col in cols:
            _logger.info("Move translations for product_template field '%s'", col)
            cr.execute(
                "alter table product_template rename column %s TO old_%s",
                (AsIs(col), AsIs(col)),
            )
            cr.execute(
                "alter table product_template add column %s jsonb", (AsIs(col), )
            )
            _logger.info("Create tranlsations for product_template field '%s' in %s", col, default_lang)
            cr.execute(
                """
                UPDATE
                    product_template
                SET
                    %s = jsonb_set('{}', '{\"%s\"}', to_jsonb(old_%s))
                """, (AsIs(col), AsIs(default_lang), AsIs(col))
            )
            for code in lang_codes:
                if code == default_lang:
                    continue
                _logger.info(
                    "Create translations for product_template field '%s' in %s",
                    col, code)
                cr.execute(
                    """
                    UPDATE
                        product_template
                    SET %s = jsonb_set(product_template.%s, '{\"%s\"}', to_jsonb(value))
                    FROM ir_translation
                    WHERE
                        res_id = product_template.id
                        and ir_translation.type = 'model'
                        and lang = %s
                        and ir_translation.name = 'product.template,%s'
                    
                    """, (AsIs(col), AsIs(col), AsIs(code), code, AsIs(col))
                )

