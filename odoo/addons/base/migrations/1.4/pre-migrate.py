# Copyright 2025 ACSONE SA/NV (<http://acsone.eu>)
# License AGPL-3.0 or later (http://www.gnu.org/licenses/agpl.html).
from odoo.tools import sql


def migrate(cr, version):
    """
    Create a table to save existing value of user_id in res.partner.
    (then it'll be deleted in post init hook)
    :param cr:
    :param version:
    :return:
    """
    create_table = """
    CREATE TABLE IF NOT EXISTS mig_res_partner_user_id_company_dependent (
        partner_id INTEGER,
        user_id INTEGER
    );"""
    filling_query = """
    INSERT INTO mig_res_partner_user_id_company_dependent (partner_id, user_id)
    SELECT id, user_id
    FROM res_partner
    WHERE user_id IS NOT NULL;"""
    clean_partner_user = "ALTER TABLE res_partner DROP COLUMN user_id;"
    cr.execute(create_table)
    cr.execute(filling_query)
    cr.execute(clean_partner_user)
